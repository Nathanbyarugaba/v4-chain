------------------------- MODULE RateLimitRecovery -------------------------
(***************************************************************************)
(* Formal TLA+ model of the dYdX v4 x/ratelimit capacity recovery, checking *)
(* that the withdrawal rate-limiter cannot PERMANENTLY freeze funds.         *)
(*                                                                          *)
(* Ground truth:                                                            *)
(*  protocol/x/ratelimit/keeper/keeper.go ProcessWithdrawal: a withdrawal    *)
(*    is rejected (ErrWithdrawalExceedsCapacity) if amount > capacity for any *)
(*    limiter; otherwise each capacity is debited by amount.                 *)
(*  protocol/x/ratelimit/util/capacity.go CalculateNewCapacityList +         *)
(*  util/baseline.go GetBaseline: each block, capacity trends toward         *)
(*    baseline = max(baseline_minimum, baseline_tvl_ppm * tvl)               *)
(*    by baseline*(dt/period) when below baseline (recovers to baseline over *)
(*    one `period`).                                                         *)
(*  protocol/x/ratelimit/types/params.go LimitParams.Validate: REJECTS       *)
(*    baseline_minimum <= 0, baseline_tvl_ppm == 0, and period == 0.         *)
(*                                                                          *)
(* Therefore baseline > 0 always (validation-enforced), so a depleted        *)
(* capacity provably recovers to a positive baseline and withdrawals up to   *)
(* the baseline become possible again -> no permanent freeze. The `zero`     *)
(* config (baseline = 0, which Validate forbids) shows the validation guard  *)
(* is load-bearing: without it, capacity is stuck at 0 forever.              *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS
    Baseline,       \* the positive baseline capacity (0 only in the forbidden config)
    RecoverStep,    \* per-block recovery amount (~ baseline/period, >=1 iff Baseline>0)
    WithdrawAmount  \* a target withdrawal amount (<= Baseline in a valid config)

VARIABLES
    capacity        \* current limiter capacity (starts fully depleted at 0)

vars == <<capacity>>

TypeOK == capacity \in 0..Baseline

Init == capacity = 0    \* worst case: capacity fully depleted by prior withdrawals

(* One block of recovery: move capacity toward baseline without crossing it. *)
Recover ==
    capacity' = IF capacity + RecoverStep < Baseline
                THEN capacity + RecoverStep
                ELSE Baseline

Next == Recover

Spec == Init /\ [][Next]_vars /\ WF_vars(Recover)

------------------------------------------------------------------------------
(* LIVENESS: a fully-depleted limiter eventually recovers enough capacity to  *)
(* allow a withdrawal of `WithdrawAmount`. HOLDS when Baseline >= WithdrawAmount *)
(* > 0 with RecoverStep > 0 (the validated case); FAILS when Baseline = 0 with *)
(* RecoverStep = 0 (the case Validate forbids) -> permanent freeze.           *)
CanWithdrawEventually == <>(capacity >= WithdrawAmount)

=============================================================================
