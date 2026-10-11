import Analysis.ScaledIntervalMul

/-!
Reciprocals and roots for the corrected CDT contour (author revision, A.4, page 204).
-/

namespace DirichletL.ScaledInterval

/-- Reciprocal enclosure, whose correctness requires a positive lower endpoint. -/
def inv (D : ℕ) (I : NonemptyInterval ℤ) : NonemptyInterval ℤ :=
  NonemptyInterval.pure ((D : ℤ) ^ 2 / I.snd) ⊔
    NonemptyInterval.pure (-((-((D : ℤ) ^ 2)) / I.fst))

theorem inv_mem {D : ℕ} (hD : 0 < D) {I : NonemptyInterval ℤ} {x : ℝ}
    (hI : 0 < I.fst) (hx : x ∈ denote D I) :
    x⁻¹ ∈ denote D (inv D I) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hlo : (0 : ℝ) < I.fst := by exact_mod_cast hI
  have hhi : 0 < I.snd := hI.trans_le I.fst_le_snd
  rw [mem_denote_iff hD] at hx
  have hDx : 0 < (D : ℝ) * x := hlo.trans_le hx.1
  have hxpos : 0 < x := (mul_pos_iff_of_pos_left hDr).1 hDx
  have heq : (D : ℝ) ^ 2 / ((D : ℝ) * x) = (D : ℝ) * x⁻¹ := by
    field_simp [ne_of_gt hDr, ne_of_gt hxpos]
  apply mem_denote_hull hD
  · calc
      _ ≤ (((D : ℤ) ^ 2 : ℤ) : ℝ) / (I.snd : ℝ) := int_ediv_le_real_div _ _ hhi
      _ = (D : ℝ) ^ 2 / (I.snd : ℝ) := by push_cast; rfl
      _ ≤ (D : ℝ) ^ 2 / ((D : ℝ) * x) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hDx hx.2
      _ = _ := heq
  · calc
      _ = (D : ℝ) ^ 2 / ((D : ℝ) * x) := heq.symm
      _ ≤ (D : ℝ) ^ 2 / (I.fst : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hlo hx.1
      _ = (((D : ℤ) ^ 2 : ℤ) : ℝ) / (I.fst : ℝ) := by push_cast; rfl
      _ ≤ _ := real_div_le_neg_int_ediv_neg _ _ hI

/-- Scale before taking integer square roots, with one outward upper unit. -/
def sqrt (D : ℕ) (I : NonemptyInterval ℤ) : NonemptyInterval ℤ :=
  NonemptyInterval.pure (Int.sqrt (I.fst * (D : ℤ))) ⊔
    NonemptyInterval.pure (Int.sqrt (I.snd * (D : ℤ)) + 1)

theorem sqrt_mem {D : ℕ} (hD : 0 < D) {I : NonemptyInterval ℤ} {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ∈ denote D I) :
    Real.sqrt x ∈ denote D (sqrt D I) := by
  have hDr : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  rw [mem_denote_iff hD] at hx
  have heq : Real.sqrt ((D : ℝ) ^ 2 * x) = (D : ℝ) * Real.sqrt x := by
    rw [Real.sqrt_mul' _ hx0, Real.sqrt_sq hDr]
  have hl : ((I.fst * (D : ℤ) : ℤ) : ℝ) ≤ (D : ℝ) ^ 2 * x := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hx.1 hDr]
  have hu : (D : ℝ) ^ 2 * x ≤ ((I.snd * (D : ℤ) : ℤ) : ℝ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hx.2 hDr]
  apply mem_denote_hull hD
  · calc
      _ ≤ Real.sqrt (((I.fst * (D : ℤ) : ℤ) : ℝ)) := int_sqrt_le_real_sqrt _
      _ ≤ Real.sqrt ((D : ℝ) ^ 2 * x) := Real.sqrt_le_sqrt hl
      _ = _ := heq
  · calc
      _ = Real.sqrt ((D : ℝ) ^ 2 * x) := heq.symm
      _ ≤ Real.sqrt (((I.snd * (D : ℤ) : ℤ) : ℝ)) := Real.sqrt_le_sqrt hu
      _ ≤ _ := by simpa only [Int.cast_add, Int.cast_one] using
          real_sqrt_le_int_sqrt_add_one (I.snd * (D : ℤ))

end DirichletL.ScaledInterval
