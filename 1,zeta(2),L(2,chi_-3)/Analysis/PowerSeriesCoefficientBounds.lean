import Analysis.PowerSeriesAnalytic

/-!
Geometric coefficient estimates for the coarse auxiliary matrix height,
CDT supplied v2 TeX 3986-3995, using Mathlib's positive-radius bound.
-/

namespace DirichletL

theorem exists_ge_one_coeff_bound_of_radius_pos {p : PowerSeries ℚ}
    (hp : 0 < (complexSeries p).radius) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, |(PowerSeries.coeff (R := ℚ) n p : ℝ)| ≤ C ^ (n + 1) := by
  obtain ⟨A, r, _, hr, hbound⟩ :=
    (complexSeries p).le_mul_pow_of_radius_pos hp
  let C : ℝ := max 1 (max A r)
  have hC : 1 ≤ C := le_max_left _ _
  have hAC : A ≤ C := (le_max_left A r).trans (le_max_right _ _)
  have hrC : r ≤ C := (le_max_right A r).trans (le_max_right _ _)
  refine ⟨C, hC, fun n => ?_⟩
  have hcoef : |(PowerSeries.coeff (R := ℚ) n p : ℝ)| ≤ A * r ^ n := by
    simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef,
      coeff_complexSeries, Complex.norm_ratCast] using hbound n
  refine hcoef.trans ?_
  rw [pow_succ']
  exact mul_le_mul hAC (pow_le_pow_left₀ hr.le hrC n)
    (pow_nonneg hr.le n) (zero_le_one.trans hC)

theorem exists_uniform_coeff_bound_of_radius_pos {ι : Type*} [Fintype ι]
    (f : ι → PowerSeries ℚ) (hf : ∀ i, 0 < (complexSeries (f i)).radius) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ i n, |(PowerSeries.coeff (R := ℚ) n (f i) : ℝ)| ≤ C ^ (n + 1) := by
  classical
  choose C hC hbound using fun i => exists_ge_one_coeff_bound_of_radius_pos (hf i)
  have hC0 (i) : 0 ≤ C i := zero_le_one.trans (hC i)
  have hsum : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => hC0 i)
  refine ⟨1 + ∑ i, C i, by linarith, fun i n => ?_⟩
  have hi : C i ≤ ∑ i, C i := Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i)
  exact (hbound i n).trans (pow_le_pow_left₀ (hC0 i) (by linarith) (n + 1))

end DirichletL
