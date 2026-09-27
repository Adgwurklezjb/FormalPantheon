import Analysis.ConsecutiveBlocks

/-!
Endpoint-correct integer cuts for CDT v2, supplied TeX 3998-4028 and
4150-4179. The ceiling convention and zero-dimension cases precede these
-/

namespace DirichletL

/-- Integer cuts for a real partition, with the first and final endpoints forced. -/
noncomputable def partitionCut {s : ℕ} (a : Fin (s + 1) → ℝ) (d : ℕ)
    (r : Fin (s + 1)) : ℕ :=
  if r = 0 then 0 else if r = Fin.last s then d else ⌈a r * d⌉₊ - 1

@[simp]
theorem partitionCut_zero {s : ℕ} (a : Fin (s + 1) → ℝ) (d : ℕ) :
    partitionCut a d 0 = 0 := by
  simp [partitionCut]

theorem partitionCut_last {s : ℕ} (hs : 0 < s) (a : Fin (s + 1) → ℝ) (d : ℕ) :
    partitionCut a d (Fin.last s) = d := by
  have hne : Fin.last s ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at this
    omega
  simp [partitionCut, hne]

theorem partitionCut_le_dim {s : ℕ} {a : Fin (s + 1) → ℝ}
    (ha : Monotone a) (ha1 : a (Fin.last s) = 1) (d : ℕ) (r : Fin (s + 1)) :
    partitionCut a d r ≤ d := by
  unfold partitionCut
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl
  · apply (Nat.sub_le _ _).trans
    apply Nat.ceil_le.mpr
    have har : a r ≤ 1 := by simpa only [ha1] using ha (Fin.le_last r)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right har (Nat.cast_nonneg d)

theorem monotone_partitionCut {s : ℕ} {a : Fin (s + 1) → ℝ}
    (ha : Monotone a) (ha1 : a (Fin.last s) = 1) (d : ℕ) :
    Monotone (partitionCut a d) := by
  intro i j hij
  by_cases hi0 : i = 0
  · subst i
    rw [partitionCut_zero]
    exact Nat.zero_le _
  have hj0 : j ≠ 0 := by
    intro hj
    apply hi0
    apply Fin.ext
    have hval := hij
    change i.val ≤ j.val at hval
    simp only [hj, Fin.val_zero] at hval
    simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hval
  by_cases hjlast : j = Fin.last s
  · simp only [partitionCut, if_neg hj0, if_pos hjlast]
    exact partitionCut_le_dim ha ha1 d i
  have hilast : i ≠ Fin.last s := by
    intro hi
    apply hjlast
    exact le_antisymm (Fin.le_last j) (by simpa only [hi] using hij)
  simp only [partitionCut, if_neg hi0, if_neg hj0, if_neg hilast, if_neg hjlast]
  exact Nat.sub_le_sub_right
    (Nat.ceil_mono (mul_le_mul_of_nonneg_right (ha hij) (Nat.cast_nonneg d))) 1

theorem partitionCut_bounds {s : ℕ} {a : Fin (s + 1) → ℝ}
    (ha : Monotone a) (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1)
    (d : ℕ) (r : Fin (s + 1)) :
    (partitionCut a d r : ℝ) ≤ a r * d ∧ a r * d ≤ (partitionCut a d r : ℝ) + 1 := by
  unfold partitionCut
  split_ifs with h0 hlast
  · subst r
    simp [ha0]
  · subst r
    simp [ha1]
  · have hx0 : 0 ≤ a r * d := by
      apply mul_nonneg _ (Nat.cast_nonneg d)
      simpa only [ha0] using ha (Fin.zero_le r)
    by_cases hx : a r * d = 0
    · simp [hx]
    have hpos : 0 < a r * d := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hceil : 1 ≤ ⌈a r * d⌉₊ := Nat.one_le_ceil_iff.mpr hpos
    rw [Nat.cast_sub hceil, Nat.cast_one]
    constructor
    · linarith [Nat.ceil_lt_add_one hx0]
    · linarith [Nat.le_ceil (a r * d)]

theorem partitionCut_le_iff {s d : ℕ} {a : Fin (s + 1) → ℝ}
    (ha0 : a 0 = 0) (r : Fin (s + 1)) (hr : r ≠ Fin.last s) (i : Fin d) :
    partitionCut a d r ≤ i.val ↔ a r * d ≤ (i.val : ℝ) + 1 := by
  by_cases h0 : r = 0
  · subst r
    simp only [partitionCut_zero, ha0, zero_mul, Nat.zero_le, true_iff]
    positivity
  simp only [partitionCut, if_neg h0, if_neg hr, Nat.sub_le_iff_le_add,
    Nat.ceil_le, Nat.cast_add, Nat.cast_one]

theorem lt_partitionCut_iff {s d : ℕ} {a : Fin (s + 1) → ℝ}
    (r : Fin (s + 1)) (h0 : r ≠ 0) (hr : r ≠ Fin.last s) (i : Fin d) :
    i.val < partitionCut a d r ↔ (i.val : ℝ) + 1 < a r * d := by
  simp only [partitionCut, if_neg h0, if_neg hr, Nat.lt_sub_iff_add_lt,
    Nat.lt_ceil, Nat.cast_add, Nat.cast_one]

end DirichletL
