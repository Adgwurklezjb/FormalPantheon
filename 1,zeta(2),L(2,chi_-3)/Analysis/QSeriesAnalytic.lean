import Analysis.PowerSeriesAnalytic
import Analysis.BetaEvaluation
import Analysis.GammaEvaluation

/-!
Complex convergence of the exact beta and gamma q-series in CDT v2,
Section 11.1 (supplied `L2chi.tex` lines 7670-7680), from their already
verified real coefficient sums.
-/

namespace DirichletL

open scoped NNReal ENNReal

theorem le_radius_complexSeries_of_summable_real {p : PowerSeries ℚ} {r : ℝ≥0}
    (h : Summable (fun n => (PowerSeries.coeff (R := ℚ) n p : ℝ) * (r : ℝ) ^ n)) :
    (r : ℝ≥0∞) ≤ (complexSeries p).radius := by
  apply (complexSeries p).le_radius_of_summable_norm
  simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    norm_mul, norm_pow, Real.norm_of_nonneg r.coe_nonneg,
    Complex.norm_ratCast, Real.norm_eq_abs] using h.norm

theorem one_le_radius_complexSeries_beta :
    1 ≤ (complexSeries (PowerSeries.mk betaCoeff)).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  apply le_radius_complexSeries_of_summable_real
  simpa only [PowerSeries.coeff_mk] using
    summable_betaCoeff_mul_pow r.coe_nonneg (by exact_mod_cast hr)

theorem one_le_radius_complexSeries_gamma :
    1 ≤ (complexSeries (PowerSeries.mk gammaCoeff)).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  apply le_radius_complexSeries_of_summable_real
  simpa only [PowerSeries.coeff_mk] using
    summable_gammaCoeff_mul_pow r.coe_nonneg (by exact_mod_cast hr)

/-- The complex sum of the divisor-defined beta q-series in CDT Section 11.1. -/
noncomputable def betaAnalytic : ℂ → ℂ := (complexSeries (PowerSeries.mk betaCoeff)).sum

/-- The complex sum of the corrected gamma q-series in CDT Section 11.1. -/
noncomputable def gammaAnalytic : ℂ → ℂ := (complexSeries (PowerSeries.mk gammaCoeff)).sum

theorem hasFPowerSeriesAt_betaAnalytic :
    HasFPowerSeriesAt betaAnalytic (complexSeries (PowerSeries.mk betaCoeff)) 0 :=
  ((complexSeries (PowerSeries.mk betaCoeff)).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le one_le_radius_complexSeries_beta)).hasFPowerSeriesAt

theorem hasFPowerSeriesAt_gammaAnalytic :
    HasFPowerSeriesAt gammaAnalytic (complexSeries (PowerSeries.mk gammaCoeff)) 0 :=
  ((complexSeries (PowerSeries.mk gammaCoeff)).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le one_le_radius_complexSeries_gamma)).hasFPowerSeriesAt

theorem betaAnalytic_zero : betaAnalytic 0 = 0 := by
  have h := hasFPowerSeriesAt_betaAnalytic.coeff_zero (fun _ => 1)
  simpa [complexSeries, FormalMultilinearSeries.ofScalars, betaCoeff_zero] using h.symm

theorem gammaAnalytic_zero : gammaAnalytic 0 = 0 := by
  have h := hasFPowerSeriesAt_gammaAnalytic.coeff_zero (fun _ => 1)
  simpa [complexSeries, FormalMultilinearSeries.ofScalars, gammaCoeff] using h.symm

end DirichletL
