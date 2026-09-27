import Analysis.GammaDoubleSeries
import Foundations.Series

/-!
The real boundary limit of C in CDT v2, Section 11.1, supplied
`L2chi.tex` lines 7674-7680, via its character generating-function sum.
-/

open Filter Topology

namespace DirichletL

/-- The real character-sum expression for the Eichler integral C. -/
noncomputable def gammaLambert (q : ℝ) : ℝ :=
  gammaLambertBase q - (1 / 4 : ℝ) * gammaLambertBase (q ^ 2)

theorem gammaLambertBase_zero : gammaLambertBase 0 = 0 := by
  calc
    _ = ∑' _n : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0 <;> simp [hn]
    _ = 0 := tsum_zero

theorem gammaLambertBase_one : gammaLambertBase 1 = zetaTwo / 3 := by
  simp only [gammaLambertBase, one_pow, show (1 : ℝ) + 1 + 1 = 3 by norm_num,
    mul_one_div]
  rw [tsum_div_const, ← zetaTwo_eq_tsum]

theorem gammaLambert_zero : gammaLambert 0 = 0 := by
  simp [gammaLambert, gammaLambertBase_zero]

theorem gammaLambert_one : gammaLambert 1 = zetaTwo / 4 := by
  rw [gammaLambert, one_pow, gammaLambertBase_one]
  ring

theorem tendsto_gammaLambertBase_one :
    Tendsto gammaLambertBase (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 (zetaTwo / 3)) := by
  have hq : Tendsto (fun q : ℝ => q) (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 1) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hlim := tendsto_tsum_of_dominated_convergence
    (𝓕 := 𝓝[Set.Icc (0 : ℝ) 1] 1)
    (f := fun q : ℝ => fun n : ℕ =>
      1 / (n : ℝ) ^ 2 * (q ^ n / (1 + q ^ n + (q ^ n) ^ 2)))
    (g := fun n : ℕ => (1 / (n : ℝ) ^ 2) / 3)
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
    (fun n => ?_) ?_
  · simpa only [gammaLambertBase, tsum_div_const, ← zetaTwo_eq_tsum] using hlim
  · have hp : Tendsto (fun q : ℝ => q ^ n)
        (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 1) := by
      simpa only [one_pow] using hq.pow n
    have hr : Tendsto (fun q : ℝ => q ^ n / (1 + q ^ n + (q ^ n) ^ 2))
        (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 (1 / 3 : ℝ)) := by
      have hc : Tendsto (fun _ : ℝ => (1 : ℝ))
          (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 1) := tendsto_const_nhds
      simpa only [one_pow, show (1 : ℝ) + 1 + 1 = 3 by norm_num] using
        hp.div ((hc.add hp).add (hp.pow 2)) (by norm_num : (1 : ℝ) + 1 + 1 ^ 2 ≠ 0)
    simpa only [mul_one_div] using hr.const_mul (1 / (n : ℝ) ^ 2)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact norm_gammaLambertBase_summand_le hq.1

/-- The real radial limit of C stated in CDT v2, Section 11.1. -/
theorem tendsto_gammaLambert_one :
    Tendsto gammaLambert (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 (zetaTwo / 4)) := by
  have hsq : Tendsto (fun q : ℝ => q ^ 2) (𝓝[Set.Icc (0 : ℝ) 1] 1)
      (𝓝[Set.Icc (0 : ℝ) 1] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_id'.2 nhdsWithin_le_nhds :
        Tendsto (fun q : ℝ => q) (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 1)).pow 2
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact ⟨sq_nonneg q, by nlinarith [hq.1, hq.2]⟩
  have hlim := tendsto_gammaLambertBase_one.sub
    ((tendsto_gammaLambertBase_one.comp hsq).const_mul (1 / 4 : ℝ))
  convert hlim using 1
  ring

end DirichletL
