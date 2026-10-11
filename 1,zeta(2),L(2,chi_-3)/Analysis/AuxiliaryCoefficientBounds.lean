import Analysis.AuxiliaryCoefficientMatrix
import Arithmetic.LcmGrowth

/-!
The coarse construction height in CDT supplied v2 TeX 3986-3995.
The compiled elementary lcm bound gives a sufficient fixed height rate.
-/

namespace DirichletL

open scoped Classical

theorem abs_auxiliaryCoefficientMatrix_le {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (h D L : ℕ) (R S ε : ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hf : ∀ i n, |(PowerSeries.coeff (R := ℚ) n (f i) : ℝ)| ≤ C ^ (n + 1))
    (n : ↥(auxiliaryConstraintIndices (m * h) L R S ε))
    (p : ↥(auxiliaryFreeIndices m h D ε)) :
    |(auxiliaryCoefficientMatrix f h D L R S ε n p : ℝ)| ≤ (C ^ (L + 1)) ^ (m * h) := by
  rw [auxiliaryCoefficientMatrix_apply]
  split_ifs
  · simp only [Rat.cast_prod, Finset.abs_prod]
    have hp := Finset.prod_le_prod
      (s := Finset.univ)
      (f := fun j : Fin (m * h) =>
        |(PowerSeries.coeff (R := ℚ) ((n.val j).val - (p.val.2 j).val) (f (p.val.1 j)) : ℝ)|)
      (g := fun _ => C ^ (L + 1)) (fun j _ => abs_nonneg _)
      (fun j _ => (hf _ _).trans (pow_le_pow_right₀ hC
        (Nat.succ_le_succ ((Nat.sub_le _ _).trans (Nat.le_of_lt (n.val j).isLt)))))
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hp
  · simp only [Rat.cast_zero, abs_zero]
    positivity

theorem abs_cleared_auxiliaryCoefficientMatrix_le {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (h D L : ℕ) (R S ε : ℝ) {C : ℝ} (hC : 1 ≤ C)
    (hf : ∀ i n, |(PowerSeries.coeff (R := ℚ) n (f i) : ℝ)| ≤ C ^ (n + 1)) (M : ℤ)
    (A : Matrix ↥(auxiliaryConstraintIndices (m * h) L R S ε)
      ↥(auxiliaryFreeIndices m h D ε) ℤ)
    (hA : ∀ n p, (A n p : ℚ) =
      ((M : ℚ) * (lcmPrefix (2 * L + 6) : ℚ) ^ 3) ^ (m * h) *
        auxiliaryCoefficientMatrix f h D L R S ε n p)
    (n : ↥(auxiliaryConstraintIndices (m * h) L R S ε))
    (p : ↥(auxiliaryFreeIndices m h D ε)) :
    |(A n p : ℝ)| ≤
      (|(M : ℝ)| * (lcmPrefix (2 * L + 6) : ℝ) ^ 3 * C ^ (L + 1)) ^ (m * h) := by
  have hAR : (A n p : ℝ) =
      ((M : ℝ) * (lcmPrefix (2 * L + 6) : ℝ) ^ 3) ^ (m * h) *
        (auxiliaryCoefficientMatrix f h D L R S ε n p : ℝ) := by
    exact_mod_cast hA n p
  rw [hAR, abs_mul, abs_pow, abs_mul, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg (lcmPrefix (2 * L + 6)) :
      (0 : ℝ) ≤ (lcmPrefix (2 * L + 6) : ℝ))]
  exact (mul_le_mul_of_nonneg_left
    (abs_auxiliaryCoefficientMatrix_le f h D L R S ε hC hf n p)
    (by positivity)).trans_eq (mul_pow _ _ _).symm

theorem exists_auxiliary_clearing_height_rate {A C q : ℝ}
    (hA : 1 ≤ A) (hC : 1 ≤ C) (hq : 0 ≤ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d D L : ℕ, 0 < D → (L : ℝ) ≤ q * D + 1 →
      (A * (lcmPrefix (2 * L + 6) : ℝ) ^ 3 * C ^ (L + 1)) ^ d ≤
        Real.exp (K * d * D) := by
  have hlA : 0 ≤ Real.log A := Real.log_nonneg hA
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  let x : ℝ := 12 * Real.log 4 + Real.log C
  let y : ℝ := 36 * Real.log 4 + Real.log C + Real.log A
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  refine ⟨x * (q + 1) + y, by positivity, fun d D L hD hL => ?_⟩
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hL' : (L : ℝ) ≤ (q + 1) * D := by nlinarith
  have hT : (0 : ℝ) < lcmPrefix (2 * L + 6) := by
    exact_mod_cast lcmPrefix_pos (2 * L + 6)
  have hlog : Real.log (A * (lcmPrefix (2 * L + 6) : ℝ) ^ 3 * C ^ (L + 1)) ≤
      x * L + y := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have hlcm := log_lcmPrefix_le (2 * L + 6)
    dsimp only [x, y]
    push_cast at hlcm ⊢
    nlinarith only [hlcm]
  have hlinear : x * (L : ℝ) + y ≤ (x * (q + 1) + y) * D := by
    have hxL := mul_le_mul_of_nonneg_left hL' hx
    have hyD := mul_le_mul_of_nonneg_left hD1 hy
    nlinarith
  apply (Real.log_le_iff_le_exp (by positivity)).mp
  rw [Real.log_pow]
  calc
    _ ≤ (d : ℝ) * ((x * (q + 1) + y) * D) :=
      mul_le_mul_of_nonneg_left (hlog.trans hlinear) (Nat.cast_nonneg d)
    _ = _ := by ring

end DirichletL
