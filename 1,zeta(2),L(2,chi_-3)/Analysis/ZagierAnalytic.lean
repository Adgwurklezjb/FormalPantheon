import Analysis.PowerSeriesAnalytic
import Arithmetic.ZagierGrowth

/-!
The analytic germ of `H_A` in CDT v2, Lemma `defabc`, constructed from the
finite binomial formula for Zagier sequence C. The initial convergence
bound is exact and establishes the full open disk of radius `1/9`.
-/

namespace DirichletL

open scoped NNReal ENNReal

open Filter
open scoped Topology

/-- The complex Zagier expansion converges throughout the open disk of radius `1/9`. -/
theorem le_radius_complexSeries_zagierGenerating :
    (1 / 9 : ℝ≥0∞) ≤ (complexSeries zagierGenerating).radius := by
  suffices h : ((1 / 9 : ℝ≥0) : ℝ≥0∞) ≤ (complexSeries zagierGenerating).radius by
    simpa using h
  apply (complexSeries zagierGenerating).le_radius_of_bound (r := (1 / 9 : ℝ≥0)) 1
  intro n
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    zagierGenerating, generatingSeries, PowerSeries.coeff_mk, Rat.cast_natCast,
    Complex.norm_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  calc
    (zagierC n : ℝ) * (1 / 9) ^ n ≤ 9 ^ n * (1 / 9) ^ n := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast zagierC_le_nine_pow n)
        (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

/-- The exact `H_A` convergence radius in CDT Lemma `defabc`. -/
theorem radius_complexSeries_zagierGenerating :
    (complexSeries zagierGenerating).radius = (1 / 9 : ℝ≥0∞) := by
  apply le_antisymm _ le_radius_complexSeries_zagierGenerating
  by_contra hle
  obtain ⟨r, hr, hrr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hle)
  have hr' : (1 / 9 : ℝ) < r := by
    have hcast : ((1 / 9 : ℝ≥0) : ℝ≥0∞) < r := by simpa using hr
    exact_mod_cast hcast
  have hq : 1 < 9 * (r : ℝ) := by linarith
  have hs := (complexSeries zagierGenerating).summable_norm_mul_pow hrr
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    zagierGenerating, generatingSeries, PowerSeries.coeff_mk, Rat.cast_natCast,
    Complex.norm_natCast] at hs
  let C : ℝ := ∑' n : ℕ, (zagierC n : ℝ) * (r : ℝ) ^ n
  have hC (n : ℕ) : (zagierC n : ℝ) * (r : ℝ) ^ n ≤ C :=
    hs.le_tsum n (fun _ _ => by positivity)
  have hbound (n : ℕ) :
      1 ≤ 2 * C * (((n : ℝ) + 1) ^ 2 / (9 * (r : ℝ)) ^ n) := by
    have hlower : (9 : ℝ) ^ n ≤ 2 * ((n : ℝ) + 1) ^ 2 * (zagierC n : ℝ) := by
      exact_mod_cast nine_pow_le_zagierC_mul n
    have hprod := mul_le_mul_of_nonneg_right hlower (pow_nonneg r.coe_nonneg n)
    have hupper := mul_le_mul_of_nonneg_left (hC n)
      (by positivity : 0 ≤ 2 * ((n : ℝ) + 1) ^ 2)
    have hpow : (9 * (r : ℝ)) ^ n ≤ 2 * C * ((n : ℝ) + 1) ^ 2 := by
      rw [mul_pow]
      nlinarith [hprod, hupper]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos (by linarith : 0 < 9 * (r : ℝ)) n)).mpr
    simpa using hpow
  have hlim : Tendsto (fun n : ℕ => 2 * C * (((n : ℝ) + 1) ^ 2 /
      (9 * (r : ℝ)) ^ n)) atTop (𝓝 0) := by
    have h := (tendsto_pow_const_div_const_pow_of_one_lt 2 hq).comp
      (tendsto_add_atTop_nat 1)
    have h' := h.const_mul (2 * C * (9 * (r : ℝ)))
    convert h' using 1
    · ext n
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      field_simp
      ring
    · simp
  have : (1 : ℝ) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hbound)
  norm_num at this

/-- The complex analytic realization of the already constructed formal Zagier series. -/
noncomputable def zagierAnalytic : ℂ → ℂ := (complexSeries zagierGenerating).sum

theorem zagierAnalytic_eq_tsum (z : ℂ) :
    zagierAnalytic z = ∑' n : ℕ, (zagierC n : ℂ) * z ^ n := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n zagierGenerating : ℂ)) z = _
  simp [FormalMultilinearSeries.ofScalars_sum_eq, zagierGenerating, generatingSeries]

theorem hasFPowerSeriesOnBall_zagierAnalytic :
    HasFPowerSeriesOnBall zagierAnalytic (complexSeries zagierGenerating) 0
      (1 / 9 : ℝ≥0∞) := by
  exact ((complexSeries zagierGenerating).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1 / 9)
      le_radius_complexSeries_zagierGenerating)).mono (by norm_num)
        le_radius_complexSeries_zagierGenerating

private theorem mem_zagierAnalytic_ball {z : ℂ} (hz : ‖z‖ < 1 / 9) :
    z ∈ EMetric.ball 0 (1 / 9 : ℝ≥0∞) := by
  rw [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm]
  have he : ENNReal.ofReal (1 / 9 : ℝ) = (1 / 9 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  rw [← he]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 9)).mpr hz

theorem hasSum_zagierAnalytic {z : ℂ} (hz : ‖z‖ < 1 / 9) :
    HasSum (fun n : ℕ => (zagierC n : ℂ) * z ^ n) (zagierAnalytic z) := by
  simpa [zagierGenerating, generatingSeries] using
    hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_zagierAnalytic
      (mem_zagierAnalytic_ball hz)

theorem analyticAt_zagierAnalytic {z : ℂ} (hz : ‖z‖ < 1 / 9) :
    AnalyticAt ℂ zagierAnalytic z :=
  hasFPowerSeriesOnBall_zagierAnalytic.analyticAt_of_mem (mem_zagierAnalytic_ball hz)

theorem zagierAnalytic_zero : zagierAnalytic 0 = 1 := by
  rw [zagierAnalytic_eq_tsum]
  rw [tsum_eq_single 0]
  · simp [zagierC_zero]
  · intro n hn
    rw [zero_pow hn, mul_zero]

theorem deriv_zagierAnalytic_zero : deriv zagierAnalytic 0 = 3 := by
  have h := hasFPowerSeriesOnBall_zagierAnalytic.hasFPowerSeriesAt.deriv
  simpa [complexSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    zagierGenerating, generatingSeries, zagierC_one] using h

/-- The analytic form of the recurrence ODE from CDT equation `zagr`. -/
theorem zagierAnalytic_ode {z : ℂ} (hz : ‖z‖ < 1 / 9) :
    z * (1 - z) * (1 - 9 * z) * deriv (deriv zagierAnalytic) z +
        (1 - 20 * z + 27 * z ^ 2) * deriv zagierAnalytic z +
          (9 * z - 3) * zagierAnalytic z = 0 :=
  generatingODE_eq_zero_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_zagierAnalytic
    zagierGenerating_ode (mem_zagierAnalytic_ball hz)

end DirichletL
