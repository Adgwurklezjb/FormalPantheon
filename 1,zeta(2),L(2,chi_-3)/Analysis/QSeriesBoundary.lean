import Analysis.QSeriesAnalytic

/-!
Real values of the literal beta and gamma analytic sums from CDT v2,
-/

namespace DirichletL

theorem hasFPowerSeriesOnBall_betaAnalytic :
    HasFPowerSeriesOnBall betaAnalytic (complexSeries (PowerSeries.mk betaCoeff)) 0 1 :=
  ((complexSeries (PowerSeries.mk betaCoeff)).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le one_le_radius_complexSeries_beta)).mono
      zero_lt_one one_le_radius_complexSeries_beta

theorem hasFPowerSeriesOnBall_gammaAnalytic :
    HasFPowerSeriesOnBall gammaAnalytic (complexSeries (PowerSeries.mk gammaCoeff)) 0 1 :=
  ((complexSeries (PowerSeries.mk gammaCoeff)).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le one_le_radius_complexSeries_gamma)).mono
      zero_lt_one one_le_radius_complexSeries_gamma

private theorem complexSeries_sum_ofReal {p : PowerSeries ℚ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesOnBall f (complexSeries p) 0 1) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hs : Summable (fun n => (PowerSeries.coeff (R := ℚ) n p : ℝ) * q ^ n)) :
    f (q : ℂ) = ((∑' n, (PowerSeries.coeff (R := ℚ) n p : ℝ) * q ^ n : ℝ) : ℂ) := by
  have hq : (q : ℂ) ∈ EMetric.ball 0 1 := by
    rw [← ENNReal.ofReal_one, Metric.emetric_ball]
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hq0] using hq1
  apply (hasSum_of_hasFPowerSeriesOnBall hf hq).unique
  convert Complex.hasSum_ofReal.mpr hs.hasSum using 1
  funext n
  push_cast
  rfl

theorem betaAnalytic_ofReal {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    betaAnalytic (q : ℂ) = ((∑' n, (betaCoeff n : ℝ) * q ^ n : ℝ) : ℂ) := by
  simpa only [PowerSeries.coeff_mk] using
    complexSeries_sum_ofReal hasFPowerSeriesOnBall_betaAnalytic hq0 hq1
    (by simpa only [PowerSeries.coeff_mk] using summable_betaCoeff_mul_pow hq0 hq1)

theorem gammaAnalytic_ofReal {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    gammaAnalytic (q : ℂ) = ((∑' n, (gammaCoeff n : ℝ) * q ^ n : ℝ) : ℂ) := by
  simpa only [PowerSeries.coeff_mk] using
    complexSeries_sum_ofReal hasFPowerSeriesOnBall_gammaAnalytic hq0 hq1
    (by simpa only [PowerSeries.coeff_mk] using summable_gammaCoeff_mul_pow hq0 hq1)

end DirichletL
