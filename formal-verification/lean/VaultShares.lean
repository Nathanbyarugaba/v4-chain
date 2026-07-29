/-
  Lean 4 proofs for dYdX v4 x/vault MEGAVAULT share redemption / accounting.

  Deep code-safety companion to tla/MegavaultShares.tla. We prove the exact
  floor-division facts behind:

    protocol/x/vault/keeper/withdraw.go RedeemFromMainAndSubVaults:
        redeemedQuoteQuantums = equity * shares / totalShares        (floor)
        // reverts with ErrInsufficientRedeemedQuoteQuantums if <= 0

    protocol/x/vault/keeper/deposit.go MintShares:
        sharesToMint = quantums * totalShares / equity               (floor)
        // reverts with ErrZeroSharesToMint if == 0
        totalShares += sharesToMint ; ownerShares[o] += sharesToMint

  Findings established:
    * redeemed ≤ equity                        (no over-redemption / no minting)
    * redeemed = 0  ↔  equity*shares < total   (exact DUST-FREEZE threshold, H3)
    * equity = 0 with shares outstanding freezes every redemption (vault brick)
    * withdraw/mint preserve  totalShares = Σ ownerShares  (conservation, H6)

  Core Lean 4 only (no Mathlib). `#print axioms` at the end shows no `sorry`.
-/

namespace VaultShares

/-- Quote quantums redeemed for `shares` out of `total`, backed by `equity`
    (Go `equity * shares / totalShares`, floored). -/
def redeemed (equity shares total : Nat) : Nat := (equity * shares) / total

/-! ### No over-redemption (safety) -/

/-- Redeeming `shares ≤ total` never pays out more than the whole `equity`
    (so shares can never be inflated into extra funds). -/
theorem redeemed_le_equity {equity shares total : Nat}
    (htot : 0 < total) (hst : shares ≤ total) :
    redeemed equity shares total ≤ equity := by
  unfold redeemed
  calc (equity * shares) / total
      ≤ (equity * total) / total := Nat.div_le_div_right (Nat.mul_le_mul (Nat.le_refl equity) hst)
    _ = equity := Nat.mul_div_cancel equity htot

/-! ### H3 — exact dust-freeze threshold -/

/-- A redemption rounds down to ZERO (and therefore REVERTS in the keeper)
    exactly when `equity * shares < total`. -/
theorem redeem_zero_iff {equity shares total : Nat} (htot : 0 < total) :
    redeemed equity shares total = 0 ↔ equity * shares < total := by
  unfold redeemed
  exact Nat.div_eq_zero_iff_lt htot

/-- A redemption pays out a positive amount as soon as `equity * shares ≥ total`. -/
theorem redeem_pos_of_ge {equity shares total : Nat}
    (htot : 0 < total) (hge : total ≤ equity * shares) :
    0 < redeemed equity shares total := by
  unfold redeemed
  exact Nat.div_pos hge htot

/-- `redeemed` is monotone in the number of shares. -/
theorem redeemed_mono {equity total s s' : Nat} (h : s' ≤ s) :
    redeemed equity s' total ≤ redeemed equity s total := by
  unfold redeemed
  exact Nat.div_le_div_right (Nat.mul_le_mul (Nat.le_refl equity) h)

/-- PERMANENT DUST FREEZE (H3): if a holder's ENTIRE withdrawable stake `s`
    already floor-divides to a zero payout, then EVERY smaller withdrawal also
    pays zero — so those shares can never be converted to any positive amount. -/
theorem dust_freeze {equity total s : Nat}
    (htot : 0 < total) (hdust : equity * s < total) :
    ∀ s', s' ≤ s → redeemed equity s' total = 0 := by
  intro s' hle
  have hmono : redeemed equity s' total ≤ redeemed equity s total := redeemed_mono hle
  have hz : redeemed equity s total = 0 := (redeem_zero_iff htot).mpr hdust
  omega

/-- VAULT BRICK: once `equity` reaches 0 while shares are still outstanding,
    every redemption pays zero (and, in Go, further deposits divide-by-zero),
    so the whole megavault is frozen. -/
theorem equity_zero_bricks {shares total : Nat} :
    redeemed 0 shares total = 0 := by
  unfold redeemed; simp

/-! ### H6 — share-conservation is preserved by every state transition -/

/-- Withdraw step: the keeper does `totalShares -= s` and `ownerShares[o] -= s`;
    with the pool invariant `total = Σowners`, conservation is preserved. -/
theorem conservation_withdraw {total ownerSum s : Nat}
    (hinv : total = ownerSum) (hs : s ≤ ownerSum) :
    total - s = ownerSum - s := by
  omega

/-- Mint step: the keeper does `totalShares += m` and `ownerShares[o] += m`;
    conservation is preserved. -/
theorem conservation_mint {total ownerSum m : Nat}
    (hinv : total = ownerSum) :
    total + m = ownerSum + m := by
  omega

end VaultShares

#print axioms VaultShares.redeemed_le_equity
#print axioms VaultShares.redeem_zero_iff
#print axioms VaultShares.redeem_pos_of_ge
#print axioms VaultShares.dust_freeze
#print axioms VaultShares.equity_zero_bricks
#print axioms VaultShares.conservation_withdraw
#print axioms VaultShares.conservation_mint
