# Formal verification: hunting permanent freezing of funds

Machine-checked specifications and proofs targeting **critical bugs that
permanently freeze user funds** in the dYdX v4 protocol (`protocol/x/...`).

Two toolchains, matched to two abstraction levels:

- **TLA+ / TLC** — protocol state machines, where a *liveness* failure means
  "funds never become withdrawable again". TLC checks safety + liveness and
  emits concrete counterexample traces.
- **Lean 4** (primary) and **Coq** (independent cross-check) — the exact integer
  arithmetic / invariant-preservation lemmas behind the Go keeper code
  (uint32 wraparound, floor-division redemption, monotonic-state panics).

A small **Go** program (`corroboration/`) executes the real `math/big`
operations to corroborate the vault-arithmetic findings at runtime.

> These are formal-model + arithmetic results about the code **as written**, with
> the real-world reachability preconditions stated explicitly. See
> [`FINDINGS.md`](./FINDINGS.md) for the classified results and suggested
> mitigations. They are intended to guide maintainer review, not to assert a
> live exploit.

## Results at a glance

| Check | Config | Expectation | Meaning |
|-------|--------|-------------|---------|
| `WithdrawalGating` | `baseline` | **PASS** (exit 0) | design is correct when causes are transient & resolvable |
| `WithdrawalGating` | `H1_regress` | **FAIL** `SafetyNoPanic` (exit 12) | F2: height regression → panic-loop freeze |
| `WithdrawalGating` | `H5_unresolvable` | **FAIL** `EventuallyUnblocked` (exit 13) | F1: unresolvable neg-TNC → permanent pool freeze |
| `NegativeTncResolution` | `resolvable` | **PASS** (exit 0) | deleveraging clears neg-TNC on a two-sided market |
| `NegativeTncResolution` | `stuck` | **FAIL** `ResolvedEventually` (exit 13) | F1b: neg-TNC structurally unresolvable → F1 reachable |
| `MegavaultShares` | `invariants` | **PASS** (exit 0) | P6/P7: conservation + unlock-scheduling hold |
| `MegavaultShares` | `dust` | **FAIL** `NoDustFreeze` (exit 12) | F3/F4: equity→0 freeze + dust freeze |
| `BridgeCompletion` | `baseline` | **PASS** (exit 0) | acknowledged bridges always complete |
| `BridgeCompletion` | `disable` | **FAIL** `NeverDropped` (exit 12) | F5: bridged funds dropped if disabled mid-flight |
| Lean `WithdrawalGating.lean` | — | compiles, no `sorry` | uint32/gating arithmetic + monotonic setter |
| Lean `VaultShares.lean` | — | compiles, no `sorry` | redemption bounds, dust threshold, conservation |
| Lean `CollateralPool.lean` | — | compiles, no `sorry` | isolated pool solvency; exact stranded amount on mismatch (P8) |
| Coq `Redemption.v` | — | compiles (`Qed`) | independent cross-check of redemption/conservation |

The intended-**FAIL** checks are the vulnerability witnesses; TLC exit codes:
`0` = held, `12` = invariant (safety) violated, `13` = temporal (liveness) violated.

## Layout

```
formal-verification/
  README.md                 this file
  FINDINGS.md               classified findings + mitigations + traces
  run.sh                    reproduce everything
  tla/
    WithdrawalGating.tla     gating circuit-breaker state machine (F1/F2)
    WithdrawalGating_*.cfg    baseline / H1_regress / H5_unresolvable
    NegativeTncResolution.tla deleveraging resolution liveness (F1b -> F1 reachability)
    NegativeTncResolution_*.cfg  resolvable / stuck
    MegavaultShares.tla      megavault share accounting (F3/F4/P6/P7)
    MegavaultShares_*.cfg     invariants / dust
    BridgeCompletion.tla     x/bridge completion vs delaymsg drop (F5)
    BridgeCompletion_*.cfg    baseline / disable
    out/                      saved TLC output + counterexample traces
  lean/
    WithdrawalGating.lean    uint32 no-underflow, bounded-freeze, monotonic setter
    VaultShares.lean         redeemed≤equity, dust threshold, conservation
    CollateralPool.lean      isolated pool solvency + exact freeze quantity (P8)
  coq/
    Redemption.v             independent cross-check
  corroboration/
    main.go                  runtime evidence for the vault arithmetic
  tools/                     tla2tools.jar (gitignored; see below)
```

## Prerequisites

Verified with: **TLC 2.19**, **Lean 4.32.2** (via elan), **Coq 8.18.0**, Go 1.22.

```bash
# TLA+ (needs Java):
mkdir -p tools
curl -sSL -o tools/tla2tools.jar \
  https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar

# Lean 4 (via elan); no Mathlib required (core tactics only):
curl -sSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"

# Coq:
sudo apt-get update && sudo apt-get install -y coq
```

## Run

```bash
export PATH="$HOME/.elan/bin:$PATH"
./run.sh
```

Or individually:

```bash
# TLA+
java -cp tools/tla2tools.jar tlc2.TLC -config tla/WithdrawalGating_H5_unresolvable.cfg tla/WithdrawalGating.tla

# Lean 4 (prints `#print axioms` — expect only propext/Quot.sound/Classical.choice, no sorryAx)
lean lean/WithdrawalGating.lean
lean lean/VaultShares.lean

# Coq
( cd coq && coqc Redemption.v )

# Go runtime corroboration
( cd corroboration && go run . )
```

## Method notes / fidelity

- Each spec/proof header cites the exact `protocol/...` `file:line` it abstracts.
- TLA+ `WithdrawalGating.tla` uses a *relative-age* encoding of block heights
  (blocks-since-armed, saturating at `SeenBlocks`) so the chain height is
  effectively unbounded and no bounded-horizon liveness artifacts occur.
- Lean proofs model Go `uint32` subtraction explicitly as `(2^32 + a - b) mod 2^32`
  and are Mathlib-free (`omega`/`decide` + core `Nat` lemmas).
- The Go corroboration is standalone (`math/big` only) and does not depend on the
  protocol module. In addition, F5 has a **keeper-level regression test** against
  the real dYdX code at `protocol/x/delaymsg/keeper/bridge_freeze_f5_test.go`
  (`go test ./x/delaymsg/keeper/ -run TestF5_BridgingDisabledDuringDelay_PermanentlyFreezesFunds`),
  which drives the real bridge msg server through the real `delaymsg` dispatch and
  shows the delayed completion is dropped (funds never delivered, message deleted).
  F3 similarly has a keeper-level regression test at
  `protocol/x/vault/keeper/megavault_freeze_f3_test.go`
  (`go test ./x/vault/keeper/ -run TestF3_MegavaultEquityZero_FreezesShareholders`),
  which shows that with equity 0 and shares outstanding, withdrawals revert and
  deposits are blocked by `ErrNonPositiveEquity` (a clean error, not a panic —
  correcting an earlier draft claim).
  F2 likewise has a keeper-level regression test at
  `protocol/x/subaccounts/keeper/blockheight_regression_f2_test.go`
  (`go test ./x/subaccounts/keeper/ -run TestF2_BlockHeightRegression_PanicsOnWithdrawal`),
  showing a withdrawal panics when a negative-TNC "seen" height sits above the
  current block height (the post-regression state), while a deposit does not.
  F1's mechanism is corroborated by
  `protocol/x/subaccounts/keeper/negative_tnc_rearm_f1_test.go`
  (`go test ./x/subaccounts/keeper/ -run TestF1_NegativeTncRearmKeepsWithdrawalsBlocked`),
  showing re-arming each block keeps withdrawals blocked indefinitely while the
  freeze lifts exactly 50 blocks after re-arming stops.
  F4 has a keeper-level regression test at
  `protocol/x/vault/keeper/dust_freeze_f4_test.go`
  (`go test ./x/vault/keeper/ -run TestF4_DustHoldersCannotWithdraw`), showing a
  sub-threshold holder's withdrawals all revert when `equity < totalShares`.

### Soundness / non-vacuity

A common formal-methods pitfall is a spec that "passes" only because it never
reaches the interesting states. We guard against it with TLC action coverage
(`-coverage 1`) on the intended-PASS configs; all relevant actions fire and the
key states are reached, so the passing invariants/liveness are meaningful:

- `WithdrawalGating` baseline: `SeeNegTnc`, `Resolve` (×51), `SeeOutage`, `Tick`
  all fire (so `ntActive`/`Blocked` states are reached and `WhileActiveBlocked`
  is exercised); `AttemptWithdraw` is evaluated ×2756 and never triggers a panic
  (so `SafetyNoPanic` holds non-vacuously); `Regress` is correctly disabled
  (`AllowRegress = FALSE`).
- `MegavaultShares` invariants: `Deposit`, `Withdraw`, `Lock`, `Unlock`,
  `EquityLoss` all fire (so `Conservation` / `LockImpliesScheduled` are tested on
  real locked/unlocked states).
- `NegativeTncResolution` resolvable: `Deleverage` fires to `remaining = 0`
  (so `ResolvedEventually` is satisfied by actual progress, not vacuity).

Reproduce with e.g.
`java -cp tools/tla2tools.jar tlc2.TLC -coverage 1 -config tla/WithdrawalGating_baseline.cfg tla/WithdrawalGating.tla`.
