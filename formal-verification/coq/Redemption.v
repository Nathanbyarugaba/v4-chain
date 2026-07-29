(*
  Coq 8.18 independent cross-check of the core dYdX v4 megavault redemption /
  share-accounting facts also proven in lean/VaultShares.lean.

  Ground truth:
    protocol/x/vault/keeper/withdraw.go RedeemFromMainAndSubVaults:
        redeemedQuoteQuantums = equity * shares / totalShares   (floor)
        // reverts (ErrInsufficientRedeemedQuoteQuantums) if <= 0
    protocol/x/vault/keeper/deposit.go MintShares / withdraw counters:
        conservation totalShares = sum(ownerShares).

  Establishes:
    * redeemed <= equity                       (no over-redemption)
    * redeemed = 0  <->  equity*shares < total (exact dust-freeze threshold, H3)
    * equity = 0 => redeemed = 0               (vault brick)
    * withdraw / mint preserve conservation    (H6)
*)

Require Import PeanoNat Lia.

Definition redeemed (equity shares total : nat) : nat := Nat.div (equity * shares) total.

(* No over-redemption: paying out never exceeds the whole equity. *)
Theorem redeemed_le_equity :
  forall equity shares total,
    0 < total -> shares <= total -> redeemed equity shares total <= equity.
Proof.
  intros equity shares total Htot Hst.
  unfold redeemed.
  apply Nat.div_le_upper_bound.
  - lia.
  - rewrite (Nat.mul_comm total equity).
    apply Nat.mul_le_mono_l. exact Hst.
Qed.

(* H3: a redemption floors to zero exactly when equity*shares < total. *)
Theorem redeem_zero_iff :
  forall equity shares total,
    0 < total ->
    (redeemed equity shares total = 0 <-> equity * shares < total).
Proof.
  intros equity shares total Htot.
  unfold redeemed.
  apply Nat.div_small_iff. lia.
Qed.

(* A positive payout appears once equity*shares >= total. *)
Theorem redeem_pos_of_ge :
  forall equity shares total,
    0 < total -> total <= equity * shares -> 0 < redeemed equity shares total.
Proof.
  intros equity shares total Htot Hge.
  unfold redeemed.
  apply Nat.div_str_pos. lia.
Qed.

(* Vault brick: equity = 0 => every redemption pays zero. *)
Theorem equity_zero_bricks :
  forall shares total, redeemed 0 shares total = 0.
Proof.
  intros shares total. unfold redeemed.
  rewrite Nat.mul_0_l. apply Nat.Div0.div_0_l.
Qed.

(* H6: conservation totalShares = sum(ownerShares) is preserved by the
   withdraw step (both counters decremented by the same s). *)
Theorem conservation_withdraw :
  forall total ownerSum s,
    total = ownerSum -> total - s = ownerSum - s.
Proof. intros; lia. Qed.

(* ... and by the mint step (both counters incremented by the same m). *)
Theorem conservation_mint :
  forall total ownerSum m,
    total = ownerSum -> total + m = ownerSum + m.
Proof. intros; lia. Qed.
