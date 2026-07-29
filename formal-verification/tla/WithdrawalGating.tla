-------------------------- MODULE WithdrawalGating --------------------------
(***************************************************************************)
(* Formal TLA+ model of the dYdX v4 withdrawal / transfer GATING circuit   *)
(* breaker, hunting for PERMANENT FREEZING OF FUNDS.                        *)
(*                                                                          *)
(* Ground truth being abstracted (see FINDINGS.md for exact file:line):    *)
(*                                                                          *)
(*  protocol/x/subaccounts/keeper/subaccount.go (internalCanUpdateSub-     *)
(*  accounts, ~L560-620): on a Withdrawal/Transfer the keeper BLOCKS the    *)
(*  operation for the collateral pool when either                          *)
(*                                                                          *)
(*    negativeTncSubaccountSeen := exists &&                                *)
(*        currentBlock - lastBlockNegativeTncSubaccountSeen < 50            *)
(*    chainOutageSeen := exists &&                                          *)
(*        currentBlock - downtime.BlockInfo.Height < 50                     *)
(*                                                                          *)
(*  (50 == WITHDRAWAL_AND_TRANSFERS_BLOCKED_AFTER_NEGATIVE_TNC_SUBACCOUNT_  *)
(*   SEEN_BLOCKS, update.go:157.) Both subtractions are on Go uint32 and    *)
(*  the code PANICS when currentBlock < the stored "seen" height -- a       *)
(*  guard against uint32 underflow.                                         *)
(*                                                                          *)
(*  protocol/x/clob/keeper/deleveraging.go GateWithdrawalsIfNegativeTnc-    *)
(*  SubaccountSeen (called from abci.go EndBlock) + process_operations.go   *)
(*  :805 RE-ARM the breaker EVERY block a negative-TNC subaccount is still  *)
(*  negative: SetNegativeTncSubaccountSeenAtBlock(currentBlock).            *)
(*                                                                          *)
(* Modeling note: we track the AGE of each "seen" record (blocks since it   *)
(* was last re-armed), saturated at SeenBlocks, instead of an absolute      *)
(* block height. This makes the chain height effectively UNBOUNDED (Tick    *)
(* is always enabled) so bounded-horizon liveness artifacts cannot occur,   *)
(* while faithfully reproducing the "within SeenBlocks" window and the      *)
(* per-block re-arm.                                                        *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS
    SeenBlocks,     \* = ..._SEEN_BLOCKS (real value 50); kept small for checking
    CanResolve,     \* TRUE  -> a negative-TNC subaccount can be deleveraged away
                    \* FALSE -> models an UNRESOLVABLE negative-TNC subaccount (H5)
    AllowRegress    \* TRUE  -> allow block-height regression (restart / bad upgrade) (H1)

VARIABLES
    ntExists,   \* a negative-TNC "seen at block" record exists for the pool
    ntActive,   \* an UNRESOLVED negative-TNC subaccount currently exists
    ntAge,      \* blocks since the neg-TNC record was last (re-)armed (0..SeenBlocks)
    coExists,   \* a chain-outage record exists
    coAge,      \* blocks since the outage record was armed (0..SeenBlocks)
    seenAhead,  \* TRUE after a height regression leaves a "seen" record in the future
    panicked    \* TRUE once a keeper panic guard fires (permanent withdrawal-path freeze)

vars == <<ntExists, ntActive, ntAge, coExists, coAge, seenAhead, panicked>>

------------------------------------------------------------------------------
(* The exact block predicate the Go keeper computes (age < window).         *)
NtBlocked == ntExists /\ ntAge < SeenBlocks
CoBlocked == coExists /\ coAge < SeenBlocks
Blocked   == NtBlocked \/ CoBlocked

(* The keeper PANICS when a stored "seen" height is in the FUTURE relative   *)
(* to the current block (the uint32-underflow guard). Reachable only after  *)
(* a block-height regression while a record is armed.                       *)
PanicCond == (ntExists \/ coExists) /\ seenAhead

------------------------------------------------------------------------------
TypeOK ==
    /\ ntExists \in BOOLEAN
    /\ ntActive \in BOOLEAN
    /\ ntAge \in 0..SeenBlocks
    /\ coExists \in BOOLEAN
    /\ coAge \in 0..SeenBlocks
    /\ seenAhead \in BOOLEAN
    /\ panicked \in BOOLEAN

Init ==
    /\ ntExists = FALSE
    /\ ntActive = FALSE
    /\ ntAge = SeenBlocks       \* no record -> "old", not within window
    /\ coExists = FALSE
    /\ coAge = SeenBlocks
    /\ seenAhead = FALSE
    /\ panicked = FALSE

------------------------------------------------------------------------------
Sat(n) == IF n < SeenBlocks THEN n + 1 ELSE SeenBlocks

(* EndBlock advances the chain by one block. While a negative-TNC subaccount *)
(* is still active, the breaker is RE-ARMED (age reset to 0); otherwise the  *)
(* age grows toward SeenBlocks and the window eventually expires.            *)
Tick ==
    /\ ntAge'    = IF ntActive THEN 0 ELSE Sat(ntAge)
    /\ coAge'    = Sat(coAge)
    /\ ntExists' = (ntExists \/ ntActive)
    /\ UNCHANGED <<ntActive, coExists, seenAhead, panicked>>

(* A negative-TNC subaccount appears. Fires at most once (bounds externals). *)
SeeNegTnc ==
    /\ ~ntExists
    /\ ntActive' = TRUE
    /\ ntExists' = TRUE
    /\ ntAge'    = 0
    /\ UNCHANGED <<coExists, coAge, seenAhead, panicked>>

(* Deleveraging closes the negative-TNC subaccount (only if resolvable).     *)
Resolve ==
    /\ CanResolve
    /\ ntActive
    /\ ntActive' = FALSE
    /\ UNCHANGED <<ntExists, ntAge, coExists, coAge, seenAhead, panicked>>

(* A >=5 minute chain outage is recorded. Fires at most once.                *)
SeeOutage ==
    /\ ~coExists
    /\ coExists' = TRUE
    /\ coAge'    = 0
    /\ UNCHANGED <<ntExists, ntActive, ntAge, seenAhead, panicked>>

(* Block-height REGRESSION: restart from an older snapshot / bad upgrade     *)
(* while a "seen" record is armed leaves that record ahead of the current    *)
(* height. (H1)                                                              *)
Regress ==
    /\ AllowRegress
    /\ (ntExists \/ coExists)
    /\ ~seenAhead
    /\ seenAhead' = TRUE
    /\ UNCHANGED <<ntExists, ntActive, ntAge, coExists, coAge, panicked>>

(* A user submits a Withdrawal / Transfer. Records a permanent freeze if the *)
(* keeper would panic; otherwise no state change (blocked+retry, or success).*)
AttemptWithdraw ==
    /\ panicked' = (panicked \/ PanicCond)
    /\ UNCHANGED <<ntExists, ntActive, ntAge, coExists, coAge, seenAhead>>

Next ==
    \/ Tick
    \/ SeeNegTnc
    \/ Resolve
    \/ SeeOutage
    \/ Regress
    \/ AttemptWithdraw

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Tick)
    /\ WF_vars(Resolve)
    /\ WF_vars(AttemptWithdraw)

------------------------------------------------------------------------------
(*                              PROPERTIES                                   *)

(* SAFETY: the panic guard never fires. HOLDS when AllowRegress = FALSE;     *)
(* FAILS (counterexample) when AllowRegress = TRUE  ==> H1: a block-height   *)
(* regression makes every Withdrawal/Transfer panic -> permanent freeze.     *)
SafetyNoPanic == panicked = FALSE

(* SAFETY: while an unresolved negative-TNC subaccount exists, withdrawals   *)
(* are ALWAYS blocked. Combined with "ntActive can be permanent" (H5), this  *)
(* is exactly the permanent-freeze condition.                                *)
WhileActiveBlocked == ntActive => Blocked

(* LIVENESS: withdrawals eventually re-open and stay open. HOLDS when        *)
(* CanResolve = TRUE; FAILS when CanResolve = FALSE ==> H5: an unresolvable  *)
(* negative-TNC subaccount permanently freezes the pool (breaker re-arms     *)
(* every block forever).                                                     *)
EventuallyUnblocked == <>[](~Blocked)

=============================================================================
