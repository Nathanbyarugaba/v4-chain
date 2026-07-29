/-
  Lean 4 proofs for dYdX v4 ISOLATED collateral-pool conservation.

  Ground truth:
    protocol/x/subaccounts/keeper/isolated_subaccount.go
      transferCollateralForIsolatedPerpetual:
        on Open  -> bank.SendCoins(cross  -> isolated, QuoteQuantums)
        on Close -> bank.SendCoins(isolated -> cross,  QuoteQuantums)
      Subaccount collateral is updated separately (in x/subaccounts state).

  Fund-safety invariant (per collateral pool p):
        poolBankBalance[p]  =  sum of collateral of subaccounts assigned to p
  If this ever drifts, one pool becomes under-collateralized and withdrawals /
  transfers for that pool cannot all be honored => funds frozen.

  We prove the transfer primitive is conservative, that the invariant is
  preserved WHEN the bank-transfer amount equals the assigned-collateral delta,
  and — crucially — that any MISMATCH between the bank amount `x` and the
  assigned-collateral delta `y` skews the two pools by EXACTLY `y - x` and
  `x - y`, i.e. leaves one pool short by |x - y| (the permanently stranded
  amount). This pinpoints the exact quantity a reviewer must confirm always
  matches: `stateTransition.QuoteQuantums` vs the subaccount's collateral delta.

  Signed integers (collateral deltas may be negative). Core Lean 4, `omega` only.
-/

namespace CollateralPool

/-- The solvency skew of a pool: bank balance minus the collateral actually
    assigned to (owned by) the subaccounts in that pool. `0` means solvent. -/
def skew (bal assigned : Int) : Int := bal - assigned

/-- A pool-to-pool transfer of `x` neither creates nor destroys funds. -/
theorem transfer_preserves_total (cross iso x : Int) :
    (cross - x) + (iso + x) = cross + iso := by omega

/-- If both pools start solvent and the bank transfer amount equals the
    assigned-collateral delta (`x` on both sides), both pools stay solvent. -/
theorem match_preserves_solvency (cross iso sumCross sumIso x : Int)
    (hc : skew cross sumCross = 0) (hi : skew iso sumIso = 0) :
    skew (cross - x) (sumCross - x) = 0 ∧ skew (iso + x) (sumIso + x) = 0 := by
  unfold skew at *; constructor <;> omega

/-- MISMATCH: if the bank moves `x` but the assigned collateral moves `y`, the
    cross pool's skew becomes `y - x` and the isolated pool's becomes `x - y`
    (starting from solvent). The two skews are exact negatives: one pool gains a
    phantom surplus, the other is short by the same amount. -/
theorem mismatch_skew (cross iso sumCross sumIso x y : Int)
    (hc : skew cross sumCross = 0) (hi : skew iso sumIso = 0) :
    skew (cross - x) (sumCross - y) = y - x
      ∧ skew (iso + x) (sumIso + y) = x - y := by
  unfold skew at *; constructor <;> omega

/-- Therefore ANY mismatch (`x ≠ y`) makes BOTH pools' invariants break; the
    short pool is under-collateralized by exactly `|x - y|`, which freezes that
    pool's withdrawals/transfers. -/
theorem mismatch_breaks_solvency (cross iso sumCross sumIso x y : Int)
    (hc : skew cross sumCross = 0) (hi : skew iso sumIso = 0) (hxy : x ≠ y) :
    skew (cross - x) (sumCross - y) ≠ 0 ∧ skew (iso + x) (sumIso + y) ≠ 0 := by
  unfold skew at *; constructor <;> omega

/-- Conversely, solvency of both pools after the transfer forces the amounts to
    match — a clean characterization of the safe condition. -/
theorem solvency_iff_match (cross iso sumCross sumIso x y : Int)
    (hc : skew cross sumCross = 0) (_hi : skew iso sumIso = 0) :
    (skew (cross - x) (sumCross - y) = 0) ↔ x = y := by
  unfold skew at *; omega

end CollateralPool

#print axioms CollateralPool.transfer_preserves_total
#print axioms CollateralPool.match_preserves_solvency
#print axioms CollateralPool.mismatch_skew
#print axioms CollateralPool.mismatch_breaks_solvency
#print axioms CollateralPool.solvency_iff_match
