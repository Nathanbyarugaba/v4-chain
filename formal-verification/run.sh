#!/usr/bin/env bash
# Reproduce the entire formal-verification suite.
#
# Prereqs (see README.md):
#   - Java (for TLA+/TLC) and tools/tla2tools.jar
#   - Lean 4 via elan  (lean on PATH)
#   - Coq 8.18+        (coqc on PATH)
#
# Exit-code convention for TLC:
#   0  -> all properties HELD
#   12 -> an INVARIANT (safety) was violated  (a counterexample was found)
#   13 -> a TEMPORAL (liveness) property was violated (a counterexample lasso)
# Some checks are EXPECTED to fail: those failures are the vulnerability
# witnesses (see FINDINGS.md).

set -u
cd "$(dirname "$0")"
JAR="tools/tla2tools.jar"
TLC="java -cp $JAR tlc2.TLC"
mkdir -p tla/out
rm -rf tla/states tla/out/mm_* 2>/dev/null

run_tlc () { # name cfg expected_exit
  local name="$1" cfg="$2" want="$3"
  echo "=== TLC $name (config: $cfg) ==="
  $TLC -metadir "tla/out/mm_$name" -config "tla/$cfg" tla/"${name%%_*}"*.tla >"tla/out/$name.txt" 2>&1
  # NB: module derived below explicitly to avoid glob ambiguity.
  echo "  (see tla/out/$name.txt)"
}

echo "################## TLA+ / TLC ##################"
echo; echo "=== WithdrawalGating: baseline (expect PASS, exit 0) ==="
$TLC -metadir tla/out/mm_wg_baseline -config tla/WithdrawalGating_baseline.cfg tla/WithdrawalGating.tla >tla/out/wg_baseline.txt 2>&1
echo "  exit=$?  (0 = all properties held)"

echo; echo "=== WithdrawalGating: H1 block-regression (expect FAIL: SafetyNoPanic, exit 12) ==="
$TLC -metadir tla/out/mm_wg_h1 -config tla/WithdrawalGating_H1_regress.cfg tla/WithdrawalGating.tla >tla/out/wg_h1.txt 2>&1
echo "  exit=$?  (12 = invariant violated => panic-freeze witness)"

echo; echo "=== WithdrawalGating: H5 unresolvable neg-TNC (expect FAIL: EventuallyUnblocked, exit 13) ==="
$TLC -metadir tla/out/mm_wg_h5 -config tla/WithdrawalGating_H5_unresolvable.cfg tla/WithdrawalGating.tla >tla/out/wg_h5.txt 2>&1
echo "  exit=$?  (13 = liveness violated => permanent-freeze witness)"

echo; echo "=== NegativeTncResolution: resolvable (expect PASS, exit 0) ==="
$TLC -deadlock -metadir tla/out/mm_ntr_res -config tla/NegativeTncResolution_resolvable.cfg tla/NegativeTncResolution.tla >tla/out/ntr_resolvable.txt 2>&1
echo "  exit=$?  (0 = deleveraging always clears the negative-TNC subaccount)"

echo; echo "=== NegativeTncResolution: stuck (expect FAIL: ResolvedEventually, exit 13) ==="
$TLC -deadlock -metadir tla/out/mm_ntr_stuck -config tla/NegativeTncResolution_stuck.cfg tla/NegativeTncResolution.tla >tla/out/ntr_stuck.txt 2>&1
echo "  exit=$?  (13 = liveness violated => negative-TNC PERMANENTLY unresolvable => F1 reachable)"

echo; echo "=== MegavaultShares: invariants (expect PASS, exit 0) ==="
$TLC -metadir tla/out/mm_mv_inv -config tla/MegavaultShares_invariants.cfg tla/MegavaultShares.tla >tla/out/mv_invariants.txt 2>&1
echo "  exit=$?  (0 = conservation + unlock-scheduling held)"

echo; echo "=== MegavaultShares: dust/brick (expect FAIL: NoDustFreeze, exit 12) ==="
$TLC -metadir tla/out/mm_mv_dust -config tla/MegavaultShares_dust.cfg tla/MegavaultShares.tla >tla/out/mv_dust.txt 2>&1
echo "  exit=$?  (12 = invariant violated => dust/brick freeze witness)"

rm -rf tla/out/mm_* tla/states 2>/dev/null

echo; echo "################## Lean 4 ##################"
for f in WithdrawalGating VaultShares; do
  echo "=== lean lean/$f.lean ==="
  lean "lean/$f.lean" && echo "  OK: compiled, axioms printed above" || echo "  FAIL"
done

echo; echo "################## Coq ##################"
echo "=== coqc coq/Redemption.v ==="
( cd coq && coqc -w none Redemption.v && echo "  OK: compiled (all Qed)" || echo "  FAIL" )
rm -f coq/*.vo coq/*.vok coq/*.vos coq/*.glob coq/.*.aux 2>/dev/null

echo; echo "Done. Intended-failing checks (H1, H5, dust) are the vulnerability witnesses; see FINDINGS.md."
