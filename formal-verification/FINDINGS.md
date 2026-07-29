# Findings — Permanent Freezing of Funds (formal verification)

This document reports permanent-fund-freeze conditions in the dYdX v4 protocol
that were **formally demonstrated** by the specs/proofs in this directory
(TLA+/TLC for protocol state machines; Lean 4 + Coq for the underlying integer
arithmetic), plus lightweight Go runtime corroboration.

**Status of each item is classified honestly:**

- `CONFIRMED (logic)` — the property is a machine-checked fact about the code's
  logic/arithmetic as written (model faithfully abstracts the cited Go source).
- `REACHABILITY` — the *real-world* precondition needed to trigger it on a live
  chain, and how plausible it is. These items warrant maintainer review to
  decide exploitability; I did not run a full validator to trigger them.
- `MITIGATED` / `POSITIVE` — checked properties that HOLD (no bug), documented so
  the audit surface is complete.

Model ↔ code fidelity: each spec header lists the exact `file:line` it abstracts.
The models were written after reading those functions; the Go corroboration
(`corroboration/`) executes the real `math/big` operations to confirm behavior.

---

## Summary table

| ID | Title | Severity | Status | Evidence |
|----|-------|----------|--------|----------|
| F1 | Unresolvable negative-TNC subaccount permanently freezes an entire collateral pool | **High** | CONFIRMED (logic; mechanism corroborated at runtime); REACHABILITY confirmed for one-sided/illiquid markets (see F1b) | `tla/out/wg_h5.txt`, `tla/out/ntr_stuck.txt`, Lean `rearm_always_blocked`+`freeze_is_bounded`, Go test `x/subaccounts/keeper/negative_tnc_rearm_f1_test.go` |
| F1b | Negative-TNC subaccount is structurally UNRESOLVABLE when the opposite side lacks overlapping-bankruptcy-price counterparties (no insurance/socialized-loss fallback) | **High** | CONFIRMED (logic) — this is the reachability driver for F1 | `tla/out/ntr_stuck.txt` |
| F2 | Block-height regression makes every withdrawal/transfer panic (chain-halt freeze) | **Medium** | CONFIRMED (logic **+ runtime**); REACHABILITY gated on height regression | `tla/out/wg_h1.txt`, Lean `regression_causes_panic`, Go regression test `x/subaccounts/keeper/blockheight_regression_f2_test.go` |
| F3 | Megavault freezes shareholders if equity reaches ≤0 with shares outstanding (all withdrawals pay 0 and revert; deposits blocked by `ErrNonPositiveEquity`, so no recovery via the normal path) | **Medium** | CONFIRMED (logic + runtime) | `tla/out/mv_dust.txt`, Lean `equity_zero_bricks`, Coq, Go regression test `x/vault/keeper/megavault_freeze_f3_test.go` |
| F4 | Dust freeze: sub-threshold holders can never withdraw a positive amount when equity < totalShares | **Low** | CONFIRMED (logic + runtime) | Lean `dust_freeze`/`redeem_zero_iff`, Go regression test `x/vault/keeper/dust_freeze_f4_test.go` |
| F5 | Bridged-in funds permanently lost if bridging is disabled during the acknowledge→complete delay window (delayed `MsgCompleteBridge` errors, rolls back, then is deleted with no retry) | **High** | CONFIRMED (logic **+ runtime**) | `tla/out/bc_disable.txt`; Go regression test `protocol/x/delaymsg/keeper/bridge_freeze_f5_test.go` |
| P5 | uint32 underflow in the gating window | n/a | MITIGATED (panic guard present) — but the guard is what turns F2 into a panic | Lean `guard_makes_agree` |
| P6 | Megavault share conservation `total = Σ owner` | n/a | POSITIVE (holds) | `tla/out/mv_invariants.txt`, Lean/Coq `conservation_*` |
| P7 | Locked megavault shares can be permanently stranded | n/a | MITIGATED (`LockShares` always schedules an unlock) | `tla/out/mv_invariants.txt` (`LockImpliesScheduled`) |
| P8 | Isolated collateral-pool solvency `poolBalance = Σ assigned collateral` | n/a | VERIFIED-SAFE iff bank-transfer amount = assigned-collateral delta; mismatch strands `|x−y|` | Lean `CollateralPool.lean` |
| P9 | Withdrawal rate-limiter (`x/ratelimit`) cannot permanently freeze funds | n/a | VERIFIED-SAFE (validation enforces `baseline > 0`, so capacity provably recovers) | `tla/out/rl_valid.txt` / `rl_zerobaseline.txt` |

---

## F1 — Unresolvable negative-TNC subaccount freezes a whole collateral pool  *(High)*

**Where.**
`protocol/x/subaccounts/keeper/subaccount.go` `internalCanUpdateSubaccounts`
(~L560–620) blocks **all** withdrawals/transfers for a collateral pool when a
negative-TNC subaccount was seen within the last
`WITHDRAWAL_AND_TRANSFERS_BLOCKED_AFTER_NEGATIVE_TNC_SUBACCOUNT_SEEN_BLOCKS = 50`
blocks (`x/subaccounts/types/update.go:157`). The window is **re-armed every
block** that a negative-TNC subaccount still exists:
`protocol/x/clob/abci.go` (EndBlock, ~L281-284) →
`protocol/x/clob/keeper/deleveraging.go` `GateWithdrawalsIfNegativeTncSubaccountSeen`
(L171) inserts a zero-fill deleveraging op, and
`protocol/x/clob/keeper/process_operations.go:805` calls
`SetNegativeTncSubaccountSeenAtBlock(ctx, perpetualId, currentBlockHeight)`.

**Freeze mechanism.** The 50-block breaker is only *temporary* if the offending
subaccount is eventually brought back to non-negative TNC by deleveraging. If it
**cannot** be resolved — e.g. no opposite-side subaccounts to deleverage against
(`OffsetSubaccountPerpetualPosition` leaves a remainder) **and** the insurance
fund is empty (`IsValidInsuranceFundDelta` blocks a negative fund) — the
subaccount stays negative-TNC, the breaker re-arms every block, and the pool's
withdrawals/transfers are frozen **indefinitely**.

**Formal evidence.**
- TLA+ (`tla/WithdrawalGating.tla`, config `..._H5_unresolvable.cfg`,
  `CanResolve = FALSE`): the invariant `WhileActiveBlocked` HOLDS (funds are
  blocked in every reachable state while active) and the liveness property
  `EventuallyUnblocked == <>[](~Blocked)` **FAILS** — TLC exit code `13`
  (`tla/out/wg_h5.txt`). Counterexample: `SeeNegTnc` then an infinite `Tick`
  stutter with `ntActive = TRUE, ntAge = 0` (blocked forever).
- Lean (`lean/WithdrawalGating.lean`): `rearm_always_blocked : blocked c c = true`
  (while re-armed to the current block, always blocked) and, dually,
  `freeze_is_bounded : last + 50 ≤ cur → blocked cur last = false` (the freeze is
  bounded **iff** `last` stops advancing). Together: freeze is permanent exactly
  when re-arming never stops, i.e. the subaccount is never resolved.
- Baseline config (`CanResolve = TRUE`) passes all properties (`tla/out/wg_baseline.txt`),
  showing the design is correct **as long as deleveraging always makes progress**.
- Go runtime corroboration of the mechanism (the single-shot-testable part):
  `protocol/x/subaccounts/keeper/negative_tnc_rearm_f1_test.go`
  (`TestF1_NegativeTncRearmKeepsWithdrawalsBlocked`, PASSING) against the real
  subaccounts keeper: re-arming `SetNegativeTncSubaccountSeenAtBlock(currentBlock)`
  every block keeps `CanUpdateSubaccounts(Withdrawal)` returning
  `WithdrawalsAndTransfersBlocked` across 60+ consecutive blocks; once re-arming
  stops, the breaker lifts at exactly `+50` blocks (`Success`). This shows the
  permanence is due solely to the per-block re-arm — which, per F1b, never stops
  when the negative-TNC subaccount is unresolvable. (The full permanent-freeze is
  a liveness property, established by the TLA+/Lean artifacts above; the Go test
  corroborates the underlying mechanism.)

**Reachability / caveats.** The freeze requires a negative-TNC subaccount that is
*structurally* unresolvable. Finding **F1b** below establishes that this is a
real, reachable state (not merely an assumption): the deleveraging code has no
guaranteed terminal resolution for a negative-TNC account, so a one-sided /
illiquid market during an extreme move suffices. On a healthy, two-sided,
liquid market deleveraging clears negative-TNC accounts quickly and the breaker
lifts (baseline / `resolvable` configs pass).

**Suggested mitigation.** Bound the total re-arm duration independently of
per-block re-arming (a hard cap on cumulative gating), and/or guarantee a
terminal resolution path (final settlement / socialized loss) that always clears
a stuck negative-TNC subaccount so the breaker provably lifts.

---

## F1b — Negative-TNC subaccount can be structurally unresolvable  *(High — reachability driver for F1)*

**Where.** `protocol/x/clob/keeper/deleveraging.go`:
- `CanDeleverageSubaccount` (~L128-165): a **negative-TNC** account is deleveraged
  **at bankruptcy price only**; the oracle-price / final-settlement path
  (`shouldDeleverageAtOraclePrice`) is gated on **non-negative** TNC, so it
  cannot help a negative-TNC account.
- `OffsetSubaccountPerpetualPosition` (~L255-405): offsets only against
  opposite-side subaccounts whose **bankruptcy prices overlap**; it counts and
  **skips** non-overlapping ones (`numSubaccountsWithNonOverlappingBankruptcyPrices`,
  explicit `TODO(CLOB-75): Support deleveraging subaccounts with non overlapping
  bankruptcy prices`), and returns immediately with the full position un-offset
  when there are `0` opposite-side subaccounts. **No insurance-fund /
  socialized-loss fallback** exists on this path.

**Consequence.** If the opposite side lacks enough offsetting quantums at
overlapping bankruptcy prices, the bankrupt position is never fully closed, so
the subaccount stays negative-TNC indefinitely — which (via F1's per-block
re-arm) permanently freezes the whole collateral pool's withdrawals.

**Formal evidence.** `tla/NegativeTncResolution.tla`:
- Config `resolvable` (`OffsetCapacity ≥ Position`): `ResolvedEventually ==
  <>(remaining = 0)` HOLDS, exit `0` (`tla/out/ntr_resolvable.txt`).
- Config `stuck` (`Position = 3`, `OffsetCapacity = 1`, no fallback):
  `ResolvedEventually` **FAILS**, exit `13` (`tla/out/ntr_stuck.txt`). Trace:
  one `Deleverage` step (`remaining 3→2`, `capacityLeft 1→0`) then an infinite
  stutter at `remaining = 2` — the position is permanently unresolvable.

**Suggested mitigation.** Provide a guaranteed terminal resolution for
negative-TNC accounts that cannot be offset (e.g. allow oracle-price / final
settlement to also close negative-TNC positions with an insurance-fund draw or
explicit socialized loss), so `remaining` provably reaches 0 and the withdrawal
breaker lifts.

---

## F2 — Block-height regression → panic on every withdrawal/transfer  *(Medium)*

**Where.** Same gating block in `subaccount.go`. Before the window check the
keeper panics:

```go
if negativeTncSubaccountExists && currentBlock < lastBlockNegativeTncSubaccountSeen { panic(...) }
if chainOutageExists          && currentBlock < downtimeInfo.BlockInfo.Height     { panic(...) }
```

and `SetNegativeTncSubaccountSeenAtBlock`
(`x/subaccounts/keeper/negative_tnc_subaccount.go`) itself panics if the new
height is below the stored one. These guard against Go `uint32` underflow of
`currentBlock - lastSeen`.

**Freeze mechanism.** If a persisted "seen" height ever ends up **greater than**
the current block height while a record is armed, the guard fires on *every*
Withdrawal/Transfer — a deterministic panic loop that halts the withdrawal path
(and, since it panics in the update path, blocks the affected flows chain-wide).

**Formal evidence.**
- TLA+ (config `..._H1_regress.cfg`, `AllowRegress = TRUE`): `SafetyNoPanic`
  **FAILS**, TLC exit `12` (`tla/out/wg_h1.txt`). Trace: `SeeNegTnc → Regress →
  AttemptWithdraw ⇒ panicked = TRUE`. With `AllowRegress = FALSE` the invariant
  HOLDS (baseline).
- Lean: `regression_causes_panic : newHeight < stored → setSeen stored newHeight
  = .error () ∧ guardFires newHeight stored = true` (both the setter and the
  withdrawal guard fire). `no_panic_when_monotone` proves the invariant
  `stored ≤ blockHeight` is preserved and no panic occurs **as long as** heights
  are monotone non-decreasing. `regression_unguarded_wrong` shows why the guard
  exists: without it, a 1-block regression makes the raw uint32 expression
  silently report `not blocked`.
- Go runtime regression test `protocol/x/subaccounts/keeper/blockheight_regression_f2_test.go`
  (`TestF2_BlockHeightRegression_PanicsOnWithdrawal`, PASSING) against the real
  subaccounts keeper: with a negative-TNC "seen" height recorded above the current
  block height (the post-regression state), a `Deposit` does not panic but a
  `Withdrawal` panics on the uint32-underflow guard.

**Reachability / caveats.** Block height is normally strictly monotonic, so this
is **operationally gated**: it requires a height regression relative to persisted
state — e.g. restarting a node from an older snapshot without wiping module
state, a faulty state-migration/upgrade that lowers height, or a chain reset that
preserves the `NegativeTncSubaccountForCollateralPool...` / downtime records.
It is not reachable purely from user transactions on a correctly operated,
monotonic chain.

**Suggested mitigation.** On the withdrawal path, treat `currentBlock < seen` as
"stale record → not blocked / clear the record" instead of `panic`; and clamp
(not panic) in `SetNegativeTncSubaccountSeenAtBlock`. A panic here converts a
recoverable state anomaly into a hard freeze.

---

## F3 — Megavault freezes shareholders when equity hits ≤0 with shares outstanding  *(Medium)*

> **Correction (found via the runtime regression test below).** An earlier draft
> of this finding claimed `MintShares` divides by zero and panics when equity is
> 0. That is **wrong**: `MintShares` guards `equity.Sign() <= 0` and returns
> `ErrNonPositiveEquity` (a clean error, no panic). The freeze is real but is a
> revert/blocked-deposit condition, not a chain-halt panic — hence Medium, not
> Medium–High. This correction is exactly the kind of over-claim that writing the
> real-keeper test catches.

**Where.**
- `protocol/x/vault/keeper/deposit.go` `MintShares` (~L61–142): when
  `existingTotalShares > 0` it fetches `equity = GetMegavaultEquity(ctx)` and
  **returns `ErrNonPositiveEquity` if `equity.Sign() <= 0`** (before the
  `quantums * totalShares / equity` division), then returns `ErrZeroSharesToMint`
  if the quotient floors to 0. So deposits are cleanly blocked (no panic) whenever
  equity ≤ 0.
- `protocol/x/vault/keeper/withdraw.go` `RedeemFromMainAndSubVaults`:
  `redeemed = equity * shares / totalShares`; `WithdrawFromMegavault` reverts
  when `redeemed <= 0` (`ErrInsufficientRedeemedQuoteQuantums`).

**Freeze mechanism.** If megavault equity reaches `0` (or below) while shares are
still outstanding, **every** withdrawal floor-divides to `0` and reverts, **and**
new deposits (which would raise equity) are rejected with `ErrNonPositiveEquity`.
Outstanding shares therefore cannot be redeemed, and equity cannot be topped up
through the normal deposit path — shareholders are frozen out until equity is
restored by some out-of-band transfer into the megavault main subaccount.

**Formal evidence.**
- TLA+ (`tla/MegavaultShares.tla`, config `..._dust.cfg`): `NoDustFreeze`
  **FAILS**, TLC exit `12` (`tla/out/mv_dust.txt`). Minimal trace:
  `Deposit(o1,1)` → 1 share, equity 1; `EquityLoss` → equity 0; now `o1` holds a
  positive, fully-unlocked share that can never be redeemed. (The model guards
  `Deposit` when `equity = 0 ∧ totalShares > 0`, matching the Go revert.)
- Lean: `equity_zero_bricks : redeemed 0 shares total = 0` (redemption pays 0).
  Coq: same (`equity_zero_bricks`).
- Go runtime regression test `protocol/x/vault/keeper/megavault_freeze_f3_test.go`
  (`TestF3_MegavaultEquityZero_FreezesShareholders`, PASSING) against the real
  vault keeper: with megavault equity 0 and 1000 shares outstanding,
  `WithdrawFromMegavault` returns `ErrInsufficientRedeemedQuoteQuantums` and
  `MintShares` returns `ErrNonPositiveEquity` (confirming: revert + blocked
  deposit, no panic). The standalone `corroboration/` illustrates the raw
  `math/big` floor-division behavior but does NOT include the keeper's guard;
  the keeper test is the authoritative behavior.

**Reachability / caveats.** Requires megavault equity to actually reach `≤ 0`
with shares still outstanding (catastrophic vault losses). Recovery is only
possible via an equity injection that does **not** go through `MintShares`
(e.g. an operator/other transfer directly into the main vault subaccount), which
is an operational escape hatch, not a user-available one.

**Suggested mitigation.** Provide a defined recovery/redemption path when equity
is non-positive (e.g. allow a bootstrap re-mint at parity, or a governed
socialized-loss settlement), so outstanding shares are never stranded and
deposits can restore a bricked vault.

---

## F4 — Dust freeze for sub-threshold holders when equity < totalShares  *(Low)*

**Where.** `RedeemFromMainAndSubVaults` (`withdraw.go`),
`redeemed = equity * shares / totalShares` (floor), revert if `<= 0`.

**Freeze mechanism.** When `equity < totalShares` (vault worth < 1 quantum per
share), any holder whose withdrawable shares `s` satisfy `equity * s < totalShares`
gets `redeemed = 0` for `s` **and every smaller amount**, so those shares can
never be converted to a positive payout.

**Formal evidence.**
- Lean: `redeem_zero_iff : 0 < total → (redeemed equity shares total = 0 ↔
  equity*shares < total)` (exact threshold) and `dust_freeze : equity*s < total →
  ∀ s' ≤ s, redeemed equity s' total = 0` (monotone ⇒ no smaller amount helps).
  Coq `redeem_zero_iff` cross-checks.
- Go runtime: `redeemed(equity=100, shares=5, total=1000) = 0`, and no amount
  `1..5` yields a positive payout.
- Go runtime regression test `protocol/x/vault/keeper/dust_freeze_f4_test.go`
  (`TestF4_DustHoldersCannotWithdraw`, PASSING) against the real vault keeper:
  with megavault equity 1 and 1000 total shares, `WithdrawFromMegavault` reverts
  with `ErrInsufficientRedeemedQuoteQuantums` for every withdrawable amount
  (1, 100, 500, 999) — the holder can never extract a positive payout.

**Reachability / caveats.** Only bites holders below the dust threshold and only
while `equity < totalShares`; economically these are sub-1-quantum stakes.
Severity **Low** (griefing/dust), but formally those funds are unrecoverable.

**Suggested mitigation.** Allow a full-exit redemption that rounds in the
holder's favor for a 100% withdrawal, or a minimum-viable redemption path, so a
holder can always exit their entire (however small) position.

---

## F5 — Bridged-in funds permanently lost if bridging is disabled mid-flight  *(High)*

**Where.**
- `protocol/x/bridge/keeper/acknowledge_bridges.go` `AcknowledgeBridges`: for each
  recognized bridge event it schedules a delayed `MsgCompleteBridge`
  `safetyParams.DelayBlocks` in the future (via `x/delaymsg`) **and** advances
  `AcknowledgedEventInfo.NextId` past the event — so the event is **never
  re-acknowledged**.
- `protocol/x/bridge/keeper/complete_bridge.go` `CompleteBridge`: returns
  `ErrBridgingDisabled` when `safetyParams.IsDisabled` (no coins transferred).
- `protocol/x/delaymsg/keeper/dispatch.go` `DispatchMessagesForBlock`: runs each
  scheduled message in a **cached context** (`abci.RunCached` — state is rolled
  back if the handler errors, and the error is only **logged**), then in a final
  loop **unconditionally `DeleteMessage`s every** message scheduled for that block
  — no retry, no re-queue.

**Freeze mechanism.** If bridging is disabled (via `MsgUpdateSafetyParams`) at any
point during the `DelayBlocks` window between a bridge's acknowledgement and its
scheduled completion, the delayed `MsgCompleteBridge` fires while disabled,
`CompleteBridge` returns `ErrBridgingDisabled`, the cached state is discarded (the
user is **not** paid), and the delayed message is then **deleted**. Because the
event was already acknowledged (`NextId` advanced past it), it is never
re-scheduled. The user's funds — already locked/burned on the Ethereum side —
are **permanently frozen** with no on-chain recovery path.

**Formal evidence.** `tla/BridgeCompletion.tla`:
- Config `baseline` (bridging never disabled): `NeverDropped` and
  `EventuallyDelivered` both HOLD, exit `0` (`tla/out/bc_baseline.txt`).
- Config `disable` (bridging can be disabled in the window): `NeverDropped`
  **FAILS**, exit `12` (`tla/out/bc_disable.txt`). Trace:
  `Acknowledge` (delay=3) → `Tick`×3 → `Disable` → `Fire` ⇒ `phase = "dropped"`,
  `delivered = FALSE`.

**Runtime evidence (real keepers).** `protocol/x/delaymsg/keeper/bridge_freeze_f5_test.go`
(`TestF5_BridgingDisabledDuringDelay_PermanentlyFreezesFunds`, PASSING) drives the
**real** bridge msg server through the **real** `x/delaymsg` `DispatchMessagesForBlock`:
- Control (bridging enabled): recipient receives the 888 bridged tokens, the bridge
  module account is debited, and the delayed message is consumed.
- F5 (bridging disabled during the delay window before dispatch): recipient receives
  **0**, the 888 tokens remain stuck in the bridge module account, **and the delayed
  `MsgCompleteBridge` is deleted** (`GetMessage` returns not-found) — i.e. it is never
  retried, so the funds are permanently frozen.
Run: `cd protocol && go test ./x/delaymsg/keeper/ -run TestF5_BridgingDisabledDuringDelay_PermanentlyFreezesFunds -v`.

**Reachability / caveats.** Requires an authority/governance `MsgUpdateSafetyParams`
that disables bridging while at least one acknowledged bridge is still within its
delay window — a realistic security-pause scenario (bridging is often paused
precisely when something looks wrong, and in-flight deposits already exist).
Re-enabling bridging later does **not** recover the dropped completions.

**Suggested mitigation.** Do not drop delayed `MsgCompleteBridge`s on
`ErrBridgingDisabled`: either (a) make `CompleteBridge` succeed regardless of the
disable flag (the disable flag should gate *acknowledgement*, not the settlement
of already-acknowledged events), or (b) re-queue/park failed completions so they
execute once bridging is re-enabled, or (c) have `delaymsg` re-schedule a message
whose handler returned an error instead of deleting it. The regression test above
can be used to validate any such fix (the `run(true)` case should then deliver the
funds or keep the message queued rather than dropping it).

---

## Positive / mitigated results (documented for completeness)

- **P5 — uint32 underflow in the window check: MITIGATED.** Lean
  `guard_makes_agree` proves that, under the guard's precondition `last ≤ cur`,
  the raw uint32 expression equals the intended predicate. The panic guard is
  therefore correct — but note it is precisely this guard that turns a
  height-regression into F2's panic-freeze rather than a silent bypass.

- **P6 — Megavault share conservation: HOLDS.** `tla/out/mv_invariants.txt`
  (`Conservation`, `LockedLEOwned`, `NonNeg` all pass across deposit/withdraw/
  lock/unlock). Lean/Coq `conservation_withdraw` / `conservation_mint` prove the
  per-step preservation (`MintShares`/withdraw move both counters by the same
  delta). `redeemed_le_equity` proves redemptions never over-pay.

- **P7 — Locked shares cannot be permanently stranded: MITIGATED.** TLA+
  invariant `LockImpliesScheduled` HOLDS: `LockShares`
  (`x/vault/keeper/shares.go`) always schedules a `delaymsg` unlock at `tilBlock`
  before persisting the lock, so `UnlockShares` will eventually release them.

- **P9 — Withdrawal rate-limiter cannot permanently freeze funds: VERIFIED-SAFE.**
  `x/ratelimit` blocks a withdrawal when `amount > capacity`
  (`ProcessWithdrawal`), and each block moves capacity toward
  `baseline = max(baseline_minimum, baseline_tvl_ppm · tvl)`
  (`util/capacity.go`, `util/baseline.go`). Crucially, `LimitParams.Validate`
  (`types/params.go`) **rejects** `baseline_minimum <= 0`, `baseline_tvl_ppm == 0`
  and `period == 0`, so `baseline > 0` always. `tla/RateLimitRecovery.tla`
  config `valid` shows a fully-depleted capacity provably recovers to the
  baseline so withdrawals up to the baseline become possible again
  (`CanWithdrawEventually` HOLDS). The `zero-baseline` config — the state
  `Validate` forbids — shows capacity stuck at 0 forever
  (`CanWithdrawEventually` FAILS), demonstrating the validation guard is
  load-bearing. (Withdrawals *larger* than the baseline are throttled across
  periods by design; that is rate-limiting, not a freeze.)

- **P8 — Isolated collateral-pool conservation: VERIFIED-SAFE *conditionally*,
  with the exact freeze quantity pinned down.** `lean/CollateralPool.lean` proves
  the isolated open/close transfer
  (`x/subaccounts/keeper/isolated_subaccount.go transferCollateralForIsolatedPerpetual`,
  which `bank.SendCoins`es `stateTransition.QuoteQuantums` between the cross and
  isolated pool module accounts) is fund-conservative and preserves each pool's
  solvency invariant `poolBankBalance = Σ assigned-subaccount-collateral`
  **iff** the bank-transfer amount equals the subaccount's assigned-collateral
  delta (`solvency_iff_match`, `match_preserves_solvency`). It also proves that
  any mismatch of `x` (bank) vs `y` (assigned) skews the two pools by exactly
  `y - x` / `x - y` (`mismatch_skew`, `mismatch_breaks_solvency`) — i.e. one pool
  becomes short by `|x - y|`, whose withdrawals then cannot all be honored
  (frozen). **Reviewer action:** confirm `QuoteQuantums` on Open
  (`quoteQuantumsBeforeUpdate`) and on Close (`updatedSubaccount.GetUsdcPosition()`)
  always equals the corresponding change in the subaccount's collateral assigned
  to the pool; the proof shows that equality is both necessary and sufficient for
  no freeze.

---

## How to reproduce

See `README.md`. In short: `./run.sh` (Java + Lean-via-elan + Coq on PATH).
Intended-failing checks (F1/H5, F2/H1, F3–F4/dust) are the vulnerability
witnesses; everything else HOLDS.
