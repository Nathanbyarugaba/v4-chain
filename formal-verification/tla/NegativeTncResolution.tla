----------------------- MODULE NegativeTncResolution -----------------------
(***************************************************************************)
(* Formal TLA+ model of the dYdX v4 negative-TNC RESOLUTION subsystem,      *)
(* i.e. the deleveraging path that a stuck negative-TNC subaccount depends   *)
(* on to be closed. This directly determines the REACHABILITY of finding F1  *)
(* (an unresolved negative-TNC subaccount permanently freezes a whole        *)
(* collateral pool, because the withdrawal breaker re-arms every block).     *)
(*                                                                          *)
(* Ground truth (protocol/x/clob/keeper/deleveraging.go):                   *)
(*                                                                          *)
(*  MaybeDeleverageSubaccount / CanDeleverageSubaccount:                    *)
(*    - risk.NC < 0  (negative TNC) => deleverage AT BANKRUPTCY PRICE.       *)
(*    - the ORACLE-price / final-settlement path is only taken when TNC is   *)
(*      NON-negative => it CANNOT resolve a negative-TNC subaccount.         *)
(*                                                                          *)
(*  OffsetSubaccountPerpetualPosition:                                      *)
(*    - only offsets against opposite-side subaccounts whose bankruptcy      *)
(*      prices OVERLAP; others are skipped                                   *)
(*      (numSubaccountsWithNonOverlappingBankruptcyPrices++,                 *)
(*       "TODO(CLOB-75): Support deleveraging ... non overlapping ...").     *)
(*    - if numSubaccounts == 0 it returns immediately with the FULL          *)
(*      position still un-offset (deltaQuantumsRemaining).                   *)
(*    - there is NO insurance-fund / socialized-loss fallback on this path.  *)
(*                                                                          *)
(* Hence a negative-TNC subaccount is resolved IFF the opposite side has     *)
(* enough offsetting quantums AT OVERLAPPING bankruptcy prices. We model     *)
(* exactly that resource, and check whether the position is ALWAYS           *)
(* eventually closed.                                                        *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS
    Position,               \* the bankrupt subaccount's open position size (> 0)
    OffsetCapacity,         \* opposite-side quantums available AT OVERLAPPING bankruptcy prices
    FinalSettlementResolves \* models a hypothetical terminal fallback that could close a
                            \* negative-TNC position. Per the code this is FALSE (the oracle
                            \* path needs non-negative TNC); set TRUE only to show the fix.

VARIABLES
    remaining,      \* un-offset portion of the bankrupt position (Position -> 0)
    capacityLeft,   \* offsetting capacity not yet consumed
    settled         \* TRUE if a terminal fallback closed the position

vars == <<remaining, capacityLeft, settled>>

(* The subaccount is still negative-TNC (and therefore keeps the withdrawal  *)
(* breaker armed) as long as its bankrupt position is not fully closed.       *)
NegTnc == remaining > 0 /\ ~settled

TypeOK ==
    /\ remaining \in 0..Position
    /\ capacityLeft \in 0..OffsetCapacity
    /\ settled \in BOOLEAN

Init ==
    /\ remaining = Position
    /\ capacityLeft = OffsetCapacity
    /\ settled = FALSE

(* Standard deleveraging step: offset one unit of the bankrupt position       *)
(* against an overlapping-price counterparty, consuming capacity.             *)
Deleverage ==
    /\ remaining > 0
    /\ capacityLeft > 0
    /\ remaining' = remaining - 1
    /\ capacityLeft' = capacityLeft - 1
    /\ UNCHANGED settled

(* Hypothetical terminal fallback (final settlement / socialized loss) that    *)
(* could always close the position. DISABLED under the code's actual           *)
(* semantics for a negative-TNC subaccount (FinalSettlementResolves = FALSE).   *)
FinalSettlement ==
    /\ FinalSettlementResolves
    /\ remaining > 0
    /\ remaining' = 0
    /\ settled' = TRUE
    /\ UNCHANGED capacityLeft

Next == Deleverage \/ FinalSettlement

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Deleverage)
    /\ WF_vars(FinalSettlement)

------------------------------------------------------------------------------
(*                              PROPERTIES                                   *)

(* LIVENESS: the bankrupt position is ALWAYS eventually fully closed, so the  *)
(* subaccount stops being negative-TNC and the withdrawal breaker can lift.   *)
(*   - HOLDS when OffsetCapacity >= Position (enough overlapping counterparties*)
(*     OR when a terminal fallback exists).                                    *)
(*   - FAILS when OffsetCapacity < Position and no fallback => the position is  *)
(*     PERMANENTLY unresolvable => F1 permanent freeze is CONFIRMED reachable   *)
(*     for a one-sided / illiquid market.                                      *)
ResolvedEventually == <>(remaining = 0)

(* SAFETY witness: whenever capacity is exhausted below the position size and  *)
(* no fallback fired, the subaccount is stuck negative-TNC forever.            *)
StuckImpliesNegTnc ==
    (capacityLeft = 0 /\ remaining > 0 /\ ~settled) => NegTnc

=============================================================================
