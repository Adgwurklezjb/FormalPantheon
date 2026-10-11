import Analysis.PureFunctionDescent
import Analysis.AnalyticIntegrals

/-!
The normalized B6 and B7 in CDT v2, equation `defB67` (supplied TeX
lines 7431-7441). The removable quotients fix the derivatives at zero;
the literal quotient equations are asserted only on punctured neighborhoods.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

/-- The zero-constant formal integral of B3/y. -/
noncomputable def pureB6Series : PowerSeries ℚ :=
  formalIntegral (formalShift pureB3Series)

/-- The zero-constant formal integral of B4/y. -/
noncomputable def pureB7Series : PowerSeries ℚ :=
  formalIntegral (formalShift pureB4Series)

@[simp]
theorem constantCoeff_pureB6Series : PowerSeries.constantCoeff (R := ℚ) pureB6Series = 0 :=
  constantCoeff_formalIntegral _

@[simp]
theorem constantCoeff_pureB7Series : PowerSeries.constantCoeff (R := ℚ) pureB7Series = 0 :=
  constantCoeff_formalIntegral _

theorem coeff_pureB6Series_succ (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 1) pureB6Series =
      (n.factorial : ℚ) ^ 2 / (((n : ℚ) + 1) * (2 * n + 2).factorial) := by
  rw [pureB6Series, coeff_formalIntegral_succ, coeff_formalShift,
    coeff_pureB3Series_succ, pureB3QuotientCoeff, div_div]
  congr 1
  ring

theorem coeff_pureB7Series_succ (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 1) pureB7Series =
      PowerSeries.coeff (R := ℚ) (n + 1) pureB4Series / ((n : ℚ) + 1) := by
  rw [pureB7Series, coeff_formalIntegral_succ, coeff_formalShift]

theorem X_mul_derivative_pureB6Series :
    PowerSeries.X * pureB6Series.derivativeFun = pureB3Series := by
  rw [pureB6Series, derivative_formalIntegral]
  exact X_mul_formalShift_of_constantCoeff_zero constantCoeff_pureB3Series

theorem X_mul_derivative_pureB7Series :
    PowerSeries.X * pureB7Series.derivativeFun = pureB4Series := by
  rw [pureB7Series, derivative_formalIntegral]
  exact X_mul_formalShift_of_constantCoeff_zero constantCoeff_pureB4Series

theorem le_radius_complexSeries_pureB6Series : 4 ≤ (complexSeries pureB6Series).radius := by
  apply le_radius_complexSeries_pureB3Series.trans
  simpa only [pureB6Series, radius_complexSeries_formalShift] using
    le_radius_complexSeries_formalIntegral (formalShift pureB3Series)

theorem le_radius_complexSeries_pureB7Series :
    (complexSeries pureB4Series).radius ≤ (complexSeries pureB7Series).radius := by
  simpa only [pureB7Series, radius_complexSeries_formalShift] using
    le_radius_complexSeries_formalIntegral (formalShift pureB4Series)

/-- CDT's B6, with its integration constant fixed at zero. -/
noncomputable def pureB6 : ℂ → ℂ := analyticIntegral (formalShift pureB3Series)

/-- CDT's B7, with its integration constant fixed at zero. -/
noncomputable def pureB7 : ℂ → ℂ := analyticIntegral (formalShift pureB4Series)

theorem hasFPowerSeriesOnBall_pureB6 :
    HasFPowerSeriesOnBall pureB6 (complexSeries pureB6Series) 0 4 := by
  apply hasFPowerSeriesOnBall_analyticIntegral _ (by norm_num)
  simpa only [radius_complexSeries_formalShift] using le_radius_complexSeries_pureB3Series

theorem hasFPowerSeriesAt_pureB7 : HasFPowerSeriesAt pureB7 (complexSeries pureB7Series) 0 :=
  ((complexSeries pureB7Series).hasFPowerSeriesOnBall
    (pos_radius_complexSeries_pureB4Series.trans_le
      le_radius_complexSeries_pureB7Series)).hasFPowerSeriesAt

private theorem mem_pureIntegral_radius_four_ball {z : ℂ} (hz : ‖z‖ < 4) :
    z ∈ EMetric.ball 0 (4 : ℝ≥0∞) := by
  simpa only [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_ofNat, ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)] using hz

theorem analyticAt_pureB6 {z : ℂ} (hz : ‖z‖ < 4) : AnalyticAt ℂ pureB6 z :=
  hasFPowerSeriesOnBall_pureB6.analyticAt_of_mem (mem_pureIntegral_radius_four_ball hz)

theorem analyticAt_pureB7 : AnalyticAt ℂ pureB7 0 := hasFPowerSeriesAt_pureB7.analyticAt

@[simp]
theorem pureB6_zero : pureB6 0 = 0 := analyticIntegral_zero _

@[simp]
theorem pureB7_zero : pureB7 0 = 0 := analyticIntegral_zero _

/-- The literal positive-index factorial sum in CDT equation `defB67`. -/
theorem hasSum_pureB6 {z : ℂ} (hz : ‖z‖ < 4) :
    HasSum (fun n : ℕ =>
      (((n.factorial : ℚ) ^ 2 / (((n : ℚ) + 1) * (2 * n + 2).factorial) : ℚ) : ℂ) *
        z ^ (n + 1)) (pureB6 z) := by
  have h := (hasSum_nat_add_iff' 1).mpr
    (hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_pureB6
      (mem_pureIntegral_radius_four_ball hz))
  simpa only [coeff_pureB6Series_succ, Finset.sum_range_one,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_pureB6Series,
    Rat.cast_zero, zero_mul, sub_zero] using h

theorem hasDerivAt_pureB6 {z : ℂ} (hz : ‖z‖ < 4) :
    HasDerivAt pureB6 (dslope pureB3 0 z) z :=
  hasDerivAt_analyticIntegral (hasFPowerSeriesOnBall_dslope hasFPowerSeriesOnBall_pureB3)
    (mem_pureIntegral_radius_four_ball hz)

theorem eventually_hasDerivAt_pureB7 :
    ∀ᶠ z : ℂ in 𝓝 0, HasDerivAt pureB7 (dslope pureB4 0 z) z := by
  obtain ⟨r, hr⟩ := hasFPowerSeriesAt_pureB4
  filter_upwards [EMetric.ball_mem_nhds 0 hr.r_pos] with z hz
  exact hasDerivAt_analyticIntegral (hasFPowerSeriesOnBall_dslope hr) hz

@[simp]
theorem deriv_pureB6_zero : deriv pureB6 0 = 1 / 2 := by
  simpa only [dslope_same, deriv_pureB3_zero] using
    (hasDerivAt_pureB6 (by norm_num : ‖(0 : ℂ)‖ < 4)).deriv

@[simp]
theorem deriv_pureB7_zero : deriv pureB7 0 = -4 := by
  simpa only [dslope_same, deriv_pureB4_zero] using
    eventually_hasDerivAt_pureB7.self_of_nhds.deriv

theorem pureB6_deriv : deriv pureB6 =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => pureB3 z / z) := by
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 4 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
  rw [(hasDerivAt_pureB6 hz).deriv, dslope_of_ne _ hz0]
  simp [slope, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem pureB7_deriv : deriv pureB7 =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => pureB4 z / z) := by
  filter_upwards [eventually_hasDerivAt_pureB7.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hz0
  rw [hz.deriv, dslope_of_ne _ hz0]
  simp [slope, smul_eq_mul, div_eq_mul_inv, mul_comm]

end DirichletL
