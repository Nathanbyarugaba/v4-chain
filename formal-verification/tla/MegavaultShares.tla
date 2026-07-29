-------------------------- MODULE MegavaultShares --------------------------
(***************************************************************************)
(* Formal TLA+ model of dYdX v4 x/vault MEGAVAULT share accounting, hunting *)
(* for PERMANENT FREEZING OF FUNDS.                                         *)
(*                                                                          *)
(* Ground truth (see FINDINGS.md for file:line):                           *)
(*   protocol/x/vault/keeper/deposit.go  MintShares                        *)
(*     first deposit:  sharesToMint = quantums                             *)
(*     otherwise:      sharesToMint = quantums * totalShares / equity       *)
(*                     (floor; REVERTS with ErrZeroSharesToMint if == 0)    *)
(*     effect:         totalShares += mint ; ownerShares[o] += mint         *)
(*   protocol/x/vault/keeper/withdraw.go WithdrawFromMegavault /            *)
(*     RedeemFromMainAndSubVaults:                                          *)
(*     withdrawable = ownerShares[o] - totalLockedShares[o]                 *)
(*     redeemed = equity * shares / totalShares (floor)                     *)
(*                REVERTS (ErrInsufficientRedeemedQuoteQuantums) if <= 0     *)
(*     effect:  totalShares -= shares ; ownerShares[o] -= shares            *)
(*   protocol/x/vault/keeper/shares.go LockShares / UnlockShares:           *)
(*     LockShares ALWAYS schedules a delaymsg unlock at tilBlock (H4        *)
(*     mitigation); UnlockShares releases unlocks due at/before height.     *)
(*                                                                          *)
(* Properties:                                                              *)
(*   Conservation      (H6): totalShares = SUM ownerShares  -- must HOLD    *)
(*   LockedLEOwned          : locked[o] <= ownerShares[o]    -- must HOLD    *)
(*   NoDustFreeze      (H3): asserts NO fully-unlocked owner with shares>0  *)
(*                            is unable to redeem a positive amount.        *)
(*                            EXPECTED TO FAIL -> the failing state is a     *)
(*                            concrete dust-freeze witness.                 *)
(*   LockImpliesScheduled (H4): locked shares always have a scheduled       *)
(*                            unlock -- must HOLD (freeze is mitigated).    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Owners,     \* set of owner identities (keep to 2 for tractability)
    MaxShares,  \* bound on any share count
    MaxEquity,  \* bound on megavault equity (quote quantums)
    MaxDeposit  \* bound on a single deposit's quote quantums

VARIABLES
    totalShares,    \* total megavault shares
    ownerShares,    \* [Owners -> Nat] shares held per owner
    locked,         \* [Owners -> Nat] shares currently locked
    scheduled,      \* [Owners -> BOOLEAN] whether a delaymsg unlock is scheduled
    equity          \* megavault equity in quote quantums

vars == <<totalShares, ownerShares, locked, scheduled, equity>>

------------------------------------------------------------------------------
Sum(f, S) == LET g[T \in SUBSET S] == IF T = {} THEN 0
                                      ELSE LET x == CHOOSE e \in T : TRUE
                                           IN f[x] + g[T \ {x}]
             IN g[S]

TotalOwnerShares == Sum(ownerShares, Owners)

------------------------------------------------------------------------------
TypeOK ==
    /\ totalShares \in 0..(MaxShares * Cardinality(Owners))
    /\ ownerShares \in [Owners -> 0..MaxShares]
    /\ locked \in [Owners -> 0..MaxShares]
    /\ scheduled \in [Owners -> BOOLEAN]
    /\ equity \in 0..MaxEquity

Init ==
    /\ totalShares = 0
    /\ ownerShares = [o \in Owners |-> 0]
    /\ locked = [o \in Owners |-> 0]
    /\ scheduled = [o \in Owners |-> FALSE]
    /\ equity = 0

------------------------------------------------------------------------------
(* Deposit q quote quantums for owner o, minting shares per MintShares.      *)
Deposit(o, q) ==
    /\ q > 0
    /\ equity + q <= MaxEquity
    \* When totalShares>0 the Go code divides by `equity`; equity<=0 there makes
    \* big.Int.Quo panic (division by zero). We model that as the deposit being
    \* unavailable, which is exactly what makes the vault UN-recoverable once
    \* equity hits 0 with shares outstanding (see NoDustFreeze / FINDINGS.md).
    /\ (totalShares = 0 \/ equity > 0)
    /\ LET mint == IF totalShares <= 0
                   THEN q
                   ELSE (q * totalShares) \div equity
       IN /\ mint > 0                              \* else ErrZeroSharesToMint (revert)
          /\ ownerShares[o] + mint <= MaxShares
          /\ totalShares + mint <= MaxShares * Cardinality(Owners)
          /\ ownerShares' = [ownerShares EXCEPT ![o] = @ + mint]
          /\ totalShares' = totalShares + mint
          /\ equity' = equity + q
    /\ UNCHANGED <<locked, scheduled>>

(* Withdraw s shares for owner o (must be <= unlocked shares).               *)
Withdraw(o, s) ==
    /\ s > 0
    /\ s <= ownerShares[o] - locked[o]
    /\ totalShares > 0
    /\ LET redeemed == (equity * s) \div totalShares
       IN /\ redeemed > 0                          \* else revert (dust freeze)
          /\ ownerShares' = [ownerShares EXCEPT ![o] = @ - s]
          /\ totalShares' = totalShares - s
          /\ equity' = equity - redeemed
    /\ UNCHANGED <<locked, scheduled>>

(* Lock some owned shares. Faithful LockShares ALWAYS schedules an unlock.    *)
Lock(o, s) ==
    /\ s > 0
    /\ locked[o] + s <= ownerShares[o]
    /\ locked' = [locked EXCEPT ![o] = @ + s]
    /\ scheduled' = [scheduled EXCEPT ![o] = TRUE]
    /\ UNCHANGED <<totalShares, ownerShares, equity>>

(* The scheduled delaymsg fires and unlocks the owner's locked shares.        *)
Unlock(o) ==
    /\ scheduled[o]
    /\ locked[o] > 0
    /\ locked' = [locked EXCEPT ![o] = 0]
    /\ scheduled' = [scheduled EXCEPT ![o] = FALSE]
    /\ UNCHANGED <<totalShares, ownerShares, equity>>

(* The vault loses money (adverse PnL), so equity can drop below totalShares. *)
EquityLoss ==
    /\ equity > 0
    /\ equity' = equity - 1
    /\ UNCHANGED <<totalShares, ownerShares, locked, scheduled>>

Next ==
    \/ \E o \in Owners, q \in 1..MaxDeposit : Deposit(o, q)
    \/ \E o \in Owners, s \in 1..MaxShares : Withdraw(o, s)
    \/ \E o \in Owners, s \in 1..MaxShares : Lock(o, s)
    \/ \E o \in Owners : Unlock(o)
    \/ EquityLoss

Spec == Init /\ [][Next]_vars /\ WF_vars(\E o \in Owners : Unlock(o))

------------------------------------------------------------------------------
(*                              PROPERTIES                                   *)

(* H6: share accounting is conserved -- no shares are minted or destroyed    *)
(* except through the deposit/withdraw paths that move both counters.        *)
Conservation == totalShares = TotalOwnerShares

LockedLEOwned == \A o \in Owners : locked[o] <= ownerShares[o]

NonNeg ==
    /\ totalShares >= 0
    /\ \A o \in Owners : ownerShares[o] >= 0 /\ locked[o] >= 0

(* H4 mitigation: any locked shares always have a scheduled unlock, so they   *)
(* can never be permanently stranded.                                         *)
LockImpliesScheduled == \A o \in Owners : locked[o] > 0 => scheduled[o]

(* H3 witness: assert that NO fully-unlocked, non-empty owner is unable to    *)
(* redeem a positive amount for ALL withdrawable share counts. TLC is         *)
(* expected to VIOLATE this, printing a concrete dust-freeze state where an   *)
(* owner holds shares that can never be converted to a positive payout.       *)
CanRedeemSomething(o) ==
    \E s \in 1..(ownerShares[o] - locked[o]) :
        totalShares > 0 /\ (equity * s) \div totalShares > 0

NoDustFreeze ==
    \A o \in Owners :
        (ownerShares[o] > 0 /\ locked[o] = 0 /\ totalShares > 0)
            => CanRedeemSomething(o)

=============================================================================
