/-
  Lean 4 proofs for the dYdX v4 withdrawal / transfer GATING arithmetic.

  Deep code-safety companion to tla/WithdrawalGating.tla. We prove the exact
  integer facts behind:

    protocol/x/subaccounts/keeper/subaccount.go (internalCanUpdateSubaccounts,
    ~L560-620):

      // PANIC guards (uint32 underflow protection):
      if negativeTncSubaccountExists && currentBlock < lastBlockNegativeTncSubaccountSeen { panic(...) }
      if chainOutageExists          && currentBlock < downtimeInfo.BlockInfo.Height     { panic(...) }

      negativeTncSubaccountSeen := exists &&
          currentBlock - lastBlockNegativeTncSubaccountSeen < SeenBlocks   // uint32 sub
      chainOutageSeen := exists &&
          currentBlock - downtimeInfo.BlockInfo.Height       < SeenBlocks   // uint32 sub

    protocol/x/subaccounts/keeper/negative_tnc_subaccount.go
      SetNegativeTncSubaccountSeenAtBlock: panics if new blockHeight < stored value.

  All proofs are core Lean 4 (no Mathlib): `omega`, `decide`, and a few
  `Nat.*` lemmas. `#print axioms` at the bottom confirms no `sorry`/extra axioms.
-/

namespace WithdrawalGating

/-- `WITHDRAWAL_AND_TRANSFERS_BLOCKED_AFTER_NEGATIVE_TNC_SUBACCOUNT_SEEN_BLOCKS`
    (x/subaccounts/types/update.go:157). -/
def SeenBlocks : Nat := 50

/-- 2^32: the modulus of Go's `uint32` arithmetic. -/
def M : Nat := 4294967296

/-- Go `uint32` subtraction `a - b` (wraps modulo 2^32), for `a, b < M`. -/
def wrapSub (a b : Nat) : Nat := (M + a - b) % M

/-- The GUARDED / intended predicate: assuming `currentBlock ≥ lastSeen`
    (enforced by the Go panic guard), gating uses the true block difference. -/
def blocked (cur last : Nat) : Bool := decide (cur - last < SeenBlocks)

/-- The UNGUARDED predicate actually computed by the raw Go expression on
    `uint32` if the panic guard were removed. -/
def blockedWrapU32 (cur last : Nat) : Bool := decide (wrapSub cur last < SeenBlocks)

/-- Does the keeper panic guard fire on a withdrawal? (`currentBlock < lastSeen`). -/
def guardFires (cur last : Nat) : Bool := decide (cur < last)

/-! ### Basic facts about `wrapSub` (uint32 subtraction) -/

/-- No underflow: when `b ≤ a`, uint32 subtraction equals the true difference. -/
theorem wrapSub_eq_of_le {a b : Nat} (h : b ≤ a) (ha : a < M) :
    wrapSub a b = a - b := by
  unfold wrapSub
  have h1 : M + a - b = M + (a - b) := by omega
  rw [h1, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- Underflow / wraparound: when `a < b`, uint32 subtraction returns the huge
    wrapped value `M - (b - a)`. -/
theorem wrapSub_eq_of_lt {a b : Nat} (h : a < b) (hb : b < M) :
    wrapSub a b = M - (b - a) := by
  unfold wrapSub
  have h1 : M + a - b = M - (b - a) := by omega
  rw [h1]
  exact Nat.mod_eq_of_lt (by omega)

/-! ### H2 — the panic guard is exactly what makes the code correct -/

/-- With the guard's precondition (`last ≤ cur`), the raw uint32 expression and
    the intended predicate AGREE. I.e. the guard is *sufficient* for correctness. -/
theorem guard_makes_agree {cur last : Nat} (h : last ≤ cur) (hc : cur < M) :
    blockedWrapU32 cur last = blocked cur last := by
  unfold blockedWrapU32 blocked
  rw [wrapSub_eq_of_le h hc]

/-- The guard is *necessary*: a single block of height regression (the "seen"
    height is one block in the future) makes the UNGUARDED expression silently
    report `not blocked`, even though the subaccount was seen extremely recently.
    Without the panic guard this would let the gate be bypassed / mis-evaluated. -/
theorem regression_unguarded_wrong (cur : Nat) (h : cur + 1 < M) :
    blockedWrapU32 cur (cur + 1) = false := by
  unfold blockedWrapU32
  have hw : wrapSub cur (cur + 1) = M - 1 := by
    rw [wrapSub_eq_of_lt (by omega) h]; omega
  rw [hw]
  simp only [SeenBlocks, M, decide_eq_false_iff_not]
  omega

/-- Exactly in the regression region the guard fires (and it fires *only* there):
    `guardFires cur last ↔ ¬ (last ≤ cur)`. -/
theorem guardFires_iff (cur last : Nat) :
    guardFires cur last = true ↔ ¬ (last ≤ cur) := by
  unfold guardFires
  rw [decide_eq_true_iff]; omega

/-! ### H1 / bounded-freeze — the freeze is bounded IFF `last` stops advancing -/

/-- POSITIVE result: once `SeenBlocks` blocks have elapsed since the last time a
    negative-TNC subaccount was seen, the pool is NOT blocked. Hence the gate
    always lifts within 50 blocks — *provided* `last` stops being re-armed. -/
theorem freeze_is_bounded {cur last : Nat} (h : last + SeenBlocks ≤ cur) :
    blocked cur last = false := by
  unfold blocked
  rw [decide_eq_false_iff_not]
  simp only [SeenBlocks] at *
  omega

/-- The re-arm turns the bound into a PERMANENT freeze (H5 at the arithmetic
    level): while a negative-TNC subaccount persists, EndBlock keeps setting
    `last := cur`, and `blocked cur cur` is always `true`. -/
theorem rearm_always_blocked (c : Nat) : blocked c c = true := by
  unfold blocked
  simp [SeenBlocks]

/-- Characterisation of the guarded predicate. -/
theorem blocked_iff_recent (cur last : Nat) :
    blocked cur last = true ↔ cur - last < SeenBlocks := by
  unfold blocked; rw [decide_eq_true_iff]

/-! ### SetNegativeTncSubaccountSeenAtBlock monotonicity (H1 root cause) -/

/-- Model of `SetNegativeTncSubaccountSeenAtBlock`: it PANICS (here `.error`)
    when the new height is below the stored one. -/
def setSeen (stored new : Nat) : Except Unit Nat :=
  if new < stored then .error () else .ok new

/-- The setter succeeds exactly when heights are monotonically non-decreasing. -/
theorem setSeen_ok_iff (stored new : Nat) :
    (∃ v, setSeen stored new = .ok v) ↔ stored ≤ new := by
  unfold setSeen
  by_cases h : new < stored <;> simp [h] <;> omega

/-- INVARIANT PRESERVATION: if the stored "seen" height never exceeds the block
    height, and every write uses the current block height as the new value
    (`new = blockHeight`) with a non-decreasing block height, then the setter
    never panics AND the withdrawal-path panic guard (`cur < seen`) never fires.
    This is the assumption a healthy chain satisfies. -/
theorem no_panic_when_monotone
    {stored blockHeight newHeight : Nat}
    (hinv : stored ≤ blockHeight)          -- current invariant
    (hmono : blockHeight ≤ newHeight) :     -- block height does not regress
    (∃ v, setSeen stored newHeight = .ok v)  -- setSeen does not panic
      ∧ guardFires newHeight newHeight = false := by  -- withdrawal guard cannot fire at cur=seen
  constructor
  · rw [setSeen_ok_iff]; omega
  · unfold guardFires; simp

/-- CONVERSELY (H1): a block-height regression below the stored "seen" height
    makes the setter panic and the withdrawal guard fire — the permanent-freeze
    precondition. -/
theorem regression_causes_panic
    {stored newHeight : Nat} (hreg : newHeight < stored) :
    setSeen stored newHeight = .error () ∧ guardFires newHeight stored = true := by
  constructor
  · unfold setSeen; simp [hreg]
  · unfold guardFires; rw [decide_eq_true_iff]; omega

end WithdrawalGating

-- No `sorry`, no extra axioms.
#print axioms WithdrawalGating.wrapSub_eq_of_le
#print axioms WithdrawalGating.guard_makes_agree
#print axioms WithdrawalGating.regression_unguarded_wrong
#print axioms WithdrawalGating.freeze_is_bounded
#print axioms WithdrawalGating.rearm_always_blocked
#print axioms WithdrawalGating.no_panic_when_monotone
#print axioms WithdrawalGating.regression_causes_panic
