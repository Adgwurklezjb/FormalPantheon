import Analysis.WeightedCubicConvergence

/-!
Row decomposition of the full cubic lattice sums used in CDT v2,
Section 11.1, and Zagier (2009), Section 6. Source and edge checks are in
-/

namespace DirichletL

open EisensteinSeries
open scoped UpperHalfPlane

/-- Sum of the weighted cubic summands with fixed first integer coordinate. -/
noncomputable def weightedCubicRow (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) (c : ℤ) : ℂ :=
  ∑' d : ℤ, w (fun i => (![c, d] i : ZMod 6)) * eisSummand 3 ![c, d] τ

theorem weightedCubicRow_eq_tsum (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) (c : ℤ) :
    weightedCubicRow w τ c =
      ∑' d : ℤ, w (fun i => (![c, d] i : ZMod 6)) / ((c : ℂ) * τ + d) ^ 3 := by
  simp only [weightedCubicRow, eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one,
    zpow_neg, zpow_ofNat, div_eq_mul_inv]

theorem summable_norm_weightedCubicPair (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) :
    Summable (fun p : ℤ × ℤ =>
      ‖w (fun i => (![p.1, p.2] i : ZMod 6)) * eisSummand 3 ![p.1, p.2] τ‖) := by
  exact (finTwoArrowEquiv ℤ).symm.summable_iff.mpr
    (summable_norm_weightedCubicEisenstein w τ)

theorem summable_weightedCubicRowTerms (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) (c : ℤ) :
    Summable (fun d : ℤ =>
      w (fun i => (![c, d] i : ZMod 6)) * eisSummand 3 ![c, d] τ) :=
  (summable_norm_weightedCubicPair w τ).of_norm.prod_factor c

theorem summable_weightedCubicRows (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) :
    Summable (weightedCubicRow w τ) :=
  (summable_norm_weightedCubicPair w τ).of_norm.prod

theorem weightedCubicEisenstein_eq_tsum_rows (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) :
    weightedCubicEisenstein w τ = ∑' c : ℤ, weightedCubicRow w τ c := by
  rw [weightedCubicEisenstein, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  exact (summable_norm_weightedCubicPair w τ).of_norm.tsum_prod

theorem weightedCubicRow_neg (w : (Fin 2 → ZMod 6) → ℂ)
    (hw : ∀ a, w (-a) = -w a) (τ : ℍ) (c : ℤ) :
    weightedCubicRow w τ (-c) = weightedCubicRow w τ c := by
  rw [weightedCubicRow_eq_tsum, weightedCubicRow_eq_tsum]
  conv_lhs => rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro d
  change w (fun i => (![-c, -d] i : ZMod 6)) /
    ((-c : ℤ) * (τ : ℂ) + (-d : ℤ)) ^ 3 = _
  have he : (fun i => (![-c, -d] i : ZMod 6)) =
      -(fun i => (![c, d] i : ZMod 6)) := by
    ext i
    fin_cases i <;> simp
  rw [he, hw]
  have hd : ((-c : ℤ) : ℂ) * τ + ((-d : ℤ) : ℂ) = -((c : ℂ) * τ + d) := by
    push_cast
    ring
  rw [hd]
  rw [(by decide : Odd 3).neg_pow]
  simp only [neg_div, div_neg, neg_neg]

theorem weightedCubicRow_zero (w : (Fin 2 → ZMod 6) → ℂ)
    (hw : ∀ a, a 0 = 0 → w a = 0) (τ : ℍ) : weightedCubicRow w τ 0 = 0 := by
  have h : ∀ d : ℤ, w (fun i => (![(0 : ℤ), d] i : ZMod 6)) = 0 :=
    fun d => hw _ (by simp)
  simp only [weightedCubicRow, h, zero_mul, tsum_zero]

theorem weightedCubicEisenstein_eq_two_mul_tsum_rows (w : (Fin 2 → ZMod 6) → ℂ)
    (hneg : ∀ a, w (-a) = -w a) (hzero : ∀ a, a 0 = 0 → w a = 0) (τ : ℍ) :
    weightedCubicEisenstein w τ = 2 * ∑' n : ℕ, weightedCubicRow w τ (n + 1) := by
  have hp : Summable (fun n : ℕ => weightedCubicRow w τ (n + 1)) :=
    (summable_weightedCubicRows w τ).comp_injective (by
      intro n m h
      exact_mod_cast add_right_cancel h)
  have hn : Summable (fun n : ℕ => weightedCubicRow w τ (-(n + 1))) := by
    simpa only [weightedCubicRow_neg w hneg] using hp
  rw [weightedCubicEisenstein_eq_tsum_rows, tsum_of_add_one_of_neg_add_one hp hn,
    weightedCubicRow_zero w hzero]
  simp only [weightedCubicRow_neg w hneg, add_zero, two_mul]

end DirichletL
