import Foundations.Series

/-!
The real Lambert expression for B in CDT v2, Section 11.1, supplied
`L2chi.tex` line 7673, and its endpoint limit at lines 7679-7680.
Identification with the evaluated formal coefficient series is separate.
-/

open Filter Topology

namespace DirichletL

/-- The real Lambert expression for the Eichler integral B. -/
noncomputable def betaLambert (q : ℝ) : ℝ :=
  ∑' n : ℕ, chiMinusThree n / (n : ℝ) ^ 2 * (q ^ n / (1 + q ^ n))

theorem norm_betaLambert_summand_le {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ‖chiMinusThree n / (n : ℝ) ^ 2 * (q ^ n / (1 + q ^ n))‖ ≤
      1 / (n : ℝ) ^ 2 := by
  have hpow : 0 ≤ q ^ n := pow_nonneg hq n
  have hden : 0 < 1 + q ^ n := by positivity
  have hratio_nonneg : 0 ≤ q ^ n / (1 + q ^ n) := div_nonneg hpow hden.le
  have hratio_le : q ^ n / (1 + q ^ n) ≤ 1 :=
    (div_le_one hden).2 (by linarith)
  have hcoeff : ‖chiMinusThree n / (n : ℝ) ^ 2‖ ≤ 1 / (n : ℝ) ^ 2 := by
    rw [norm_div, norm_pow, Real.norm_natCast]
    exact div_le_div_of_nonneg_right (norm_chiMinusThree_le_one n) (sq_nonneg _)
  calc
    _ = ‖chiMinusThree n / (n : ℝ) ^ 2‖ * (q ^ n / (1 + q ^ n)) := by
      rw [norm_mul, Real.norm_eq_abs (q ^ n / (1 + q ^ n)),
        abs_of_nonneg hratio_nonneg]
    _ ≤ ‖chiMinusThree n / (n : ℝ) ^ 2‖ * 1 :=
      mul_le_mul_of_nonneg_left hratio_le (norm_nonneg _)
    _ = ‖chiMinusThree n / (n : ℝ) ^ 2‖ := mul_one _
    _ ≤ _ := hcoeff

theorem summable_betaLambert {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun n : ℕ => chiMinusThree n / (n : ℝ) ^ 2 *
      (q ^ n / (1 + q ^ n))) := by
  apply Summable.of_norm_bounded (g := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  exact norm_betaLambert_summand_le hq

theorem betaLambert_zero : betaLambert 0 = 0 := by
  calc
    _ = ∑' _n : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0 <;> simp [hn, chiMinusThree_zero]
    _ = 0 := tsum_zero

theorem betaLambert_one : betaLambert 1 = lTwoChiMinusThree / 2 := by
  simp only [betaLambert, one_pow, one_add_one_eq_two, mul_one_div]
  rw [tsum_div_const, ← lTwoChiMinusThree_eq_tsum]

/-- The real radial limit of B at the cusp in CDT v2, Section 11.1. -/
theorem tendsto_betaLambert_one :
    Tendsto betaLambert (𝓝[Set.Icc (0 : ℝ) 1] 1)
      (𝓝 (lTwoChiMinusThree / 2)) := by
  have hq : Tendsto (fun q : ℝ => q) (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 1) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have hlim := tendsto_tsum_of_dominated_convergence
    (𝓕 := 𝓝[Set.Icc (0 : ℝ) 1] 1)
    (f := fun q : ℝ => fun n : ℕ =>
      chiMinusThree n / (n : ℝ) ^ 2 * (q ^ n / (1 + q ^ n)))
    (g := fun n : ℕ => (chiMinusThree n / (n : ℝ) ^ 2) / 2)
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
    (fun n => ?_) ?_
  · simpa only [betaLambert, tsum_div_const, ← lTwoChiMinusThree_eq_tsum] using hlim
  · have hp : Tendsto (fun q : ℝ => q ^ n)
        (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 1) := by
      simpa only [one_pow] using hq.pow n
    have hr : Tendsto (fun q : ℝ => q ^ n / (1 + q ^ n))
        (𝓝[Set.Icc (0 : ℝ) 1] 1) (𝓝 (1 / 2 : ℝ)) := by
      simpa only [one_add_one_eq_two] using
        hp.div (tendsto_const_nhds.add hp) (by norm_num : (1 : ℝ) + 1 ≠ 0)
    simpa only [mul_one_div] using hr.const_mul (chiMinusThree n / (n : ℝ) ^ 2)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact norm_betaLambert_summand_le hq.1

end DirichletL
