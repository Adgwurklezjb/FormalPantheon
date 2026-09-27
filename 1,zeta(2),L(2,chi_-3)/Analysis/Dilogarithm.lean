import Analysis.AnalyticIntegrals

/-!
The exact logarithm and dilogarithm series in CDT v2, `sec:pureX2`
(supplied TeX lines 7311-7325). Analytic assertions use the open unit disk.
-/

namespace DirichletL

open scoped NNReal ENNReal

private theorem mem_complex_unit_ball {z : ℂ} (hz : ‖z‖ < 1) :
    z ∈ EMetric.ball 0 (1 : ℝ≥0∞) := by
  simpa only [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm,
    ENNReal.ofReal_lt_one] using hz

/-- The rational formal series of `-log(1-x)`, with zero constant coefficient. -/
noncomputable def pureLogarithmSeries : PowerSeries ℚ :=
  PowerSeries.mk (fun n => 1 / (n : ℚ))

@[simp]
theorem coeff_pureLogarithmSeries (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n pureLogarithmSeries = 1 / (n : ℚ) := by
  simp [pureLogarithmSeries]

theorem le_radius_complexSeries_pureLogarithmSeries :
    1 ≤ (complexSeries pureLogarithmSeries).radius := by
  apply (complexSeries pureLogarithmSeries).le_radius_of_bound (r := (1 : ℝ≥0)) 1
  intro n
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    coeff_pureLogarithmSeries, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    norm_div, norm_one, Complex.norm_natCast, NNReal.coe_one, one_pow, mul_one]
  rcases n with _ | n
  · norm_num
  · apply div_le_self (by norm_num : (0 : ℝ) ≤ 1)
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

theorem hasFPowerSeriesOnBall_neg_clog_one_sub :
    HasFPowerSeriesOnBall (fun z : ℂ => -Complex.log (1 - z))
      (complexSeries pureLogarithmSeries) 0 1 := by
  refine ⟨le_radius_complexSeries_pureLogarithmSeries, by norm_num, ?_⟩
  intro z hz
  have hz' : ‖z‖ < 1 := by
    simpa only [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm,
      ENNReal.ofReal_lt_one] using hz
  simpa [complexSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    div_eq_mul_inv, mul_comm] using Complex.hasSum_taylorSeries_neg_log hz'

/-- Integrating the shifted logarithm series gives the formal dilogarithm. -/
noncomputable def pureDilogarithmSeries : PowerSeries ℚ :=
  formalIntegral (formalShift pureLogarithmSeries)

@[simp]
theorem coeff_pureDilogarithmSeries (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n pureDilogarithmSeries = 1 / (n : ℚ) ^ 2 := by
  rcases n with _ | n
  · simp [pureDilogarithmSeries]
  · simp only [pureDilogarithmSeries, coeff_formalIntegral_succ, coeff_formalShift,
      coeff_pureLogarithmSeries, Nat.cast_add, Nat.cast_one, div_div, pow_two]

/-- The canonical analytic dilogarithm, normalized to zero at the origin. -/
noncomputable def pureDilogarithm : ℂ → ℂ :=
  analyticIntegral (formalShift pureLogarithmSeries)

theorem hasFPowerSeriesOnBall_pureDilogarithm :
    HasFPowerSeriesOnBall pureDilogarithm (complexSeries pureDilogarithmSeries) 0 1 := by
  have h := hasFPowerSeriesOnBall_dslope hasFPowerSeriesOnBall_neg_clog_one_sub
  exact hasFPowerSeriesOnBall_analyticIntegral _ h.r_pos h.r_le

theorem hasSum_pureDilogarithm {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ n / (n : ℂ) ^ 2) (pureDilogarithm z) := by
  simpa [div_eq_mul_inv, mul_comm] using
    hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_pureDilogarithm
      (mem_complex_unit_ball hz)

theorem analyticAt_pureDilogarithm {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ pureDilogarithm z :=
  hasFPowerSeriesOnBall_pureDilogarithm.analyticAt_of_mem (mem_complex_unit_ball hz)

@[simp]
theorem pureDilogarithm_zero : pureDilogarithm 0 = 0 := analyticIntegral_zero _

theorem hasDerivAt_pureDilogarithm {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt pureDilogarithm (dslope (fun w : ℂ => -Complex.log (1 - w)) 0 z) z :=
  hasDerivAt_analyticIntegral
    (hasFPowerSeriesOnBall_dslope hasFPowerSeriesOnBall_neg_clog_one_sub)
    (mem_complex_unit_ball hz)

theorem deriv_pureDilogarithm {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    deriv pureDilogarithm z = -Complex.log (1 - z) / z := by
  rw [(hasDerivAt_pureDilogarithm hz).deriv, dslope_of_ne _ hz0]
  simp [slope, smul_eq_mul, div_eq_mul_inv, mul_comm]

end DirichletL
