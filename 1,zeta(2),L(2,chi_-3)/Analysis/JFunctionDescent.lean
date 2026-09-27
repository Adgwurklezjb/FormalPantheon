import Analysis.JFunctionPullback
import Analysis.MobiusDescentAnalytic
import Analysis.MobiusAnalyticInvolution

/-!
The convergent B5 series of CDT v2, `defB5`, and its local analytic
trace identity with `newfunction` (supplied TeX lines 7358-7387).
The radius-four bound is strict and makes no boundary-value assertion.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

/-- The analytic B5 function obtained from the literal factorial series. -/
noncomputable def pureB5 : ℂ → ℂ := (complexSeries pureB5Series).sum

theorem hasFPowerSeriesOnBall_pureB5 :
    HasFPowerSeriesOnBall pureB5 (complexSeries pureB5Series) 0 4 :=
  ((complexSeries pureB5Series).hasFPowerSeriesOnBall
    (lt_of_lt_of_le (by norm_num) le_radius_complexSeries_pureB5Series)).mono
    (by norm_num) le_radius_complexSeries_pureB5Series

private theorem mem_radius_four_ball {z : ℂ} (hz : ‖z‖ < 4) :
    z ∈ EMetric.ball 0 (4 : ℝ≥0∞) := by
  simpa only [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_ofNat, ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 4)] using hz

theorem analyticAt_pureB5 {z : ℂ} (hz : ‖z‖ < 4) : AnalyticAt ℂ pureB5 z :=
  hasFPowerSeriesOnBall_pureB5.analyticAt_of_mem (mem_radius_four_ball hz)

/-- The source sum, with index n+1 corresponding to the source's positive index. -/
theorem hasSum_pureB5 {z : ℂ} (hz : ‖z‖ < 4) :
    HasSum (fun n => (pureB5QuotientCoeff n : ℂ) * z ^ (n + 1)) (pureB5 z) := by
  have h := (hasSum_nat_add_iff' 1).mpr
    (hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_pureB5 (mem_radius_four_ball hz))
  simpa only [pureB5Series, PowerSeries.coeff_succ_X_mul, coeff_pureB5QuotientSeries,
    Finset.sum_range_one, PowerSeries.coeff_zero_X_mul, Rat.cast_zero,
    zero_mul, sub_zero] using h

@[simp]
theorem pureB5_zero : pureB5 0 = 0 := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n pureB5Series : ℂ)) 0 = 0
  simp [FormalMultilinearSeries.ofScalarsSum_zero]

@[simp]
theorem deriv_pureB5_zero : deriv pureB5 0 = 1 := by
  simpa [coeff_complexSeries, coeff_pureB5Series_succ] using
    hasFPowerSeriesOnBall_pureB5.hasFPowerSeriesAt.deriv

theorem pureB5_eq_symmetrizedAnalytic : pureB5 = symmetrizedAnalytic pureJSeries := by
  simp only [pureB5, symmetrizedAnalytic, symmetrizedDescent_pureJSeries]

/-- The analytic positive trace identity holds on a full neighborhood of zero. -/
theorem pureB5_pullback :
    (fun z : ℂ => pureB5 (mobiusCoordinate z)) =ᶠ[𝓝 0]
      (fun z => pureJ z + pureJ (mobiusAnalyticInvolution z)) := by
  have h := symmetrizedAnalytic_pullback_of_pos_radius pureJSeries
    (lt_of_lt_of_le (by norm_num) le_radius_complexSeries_pureJSeries)
  simpa only [← pureB5_eq_symmetrizedAnalytic, mobiusCoordinate,
    mobiusAnalyticInvolution, pureJ] using h

private theorem sum_polynomial_mul {p : PowerSeries ℚ} {z a : ℂ}
    (h : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) a) (q : Polynomial ℚ) :
    (complexSeries ((q : PowerSeries ℚ) * p)).sum z = Polynomial.aeval z q * a := by
  change FormalMultilinearSeries.ofScalarsSum
    (fun n => (PowerSeries.coeff (R := ℚ) n ((q : PowerSeries ℚ) * p) : ℂ)) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simpa only [smul_eq_mul] using (hasSum_polynomial_mul h q).tsum_eq

theorem pureB5_eq_mul_quotient {z : ℂ} (hz : ‖z‖ < 4) :
    pureB5 z = z * (complexSeries pureB5QuotientSeries).sum z := by
  have hq : HasFPowerSeriesOnBall (complexSeries pureB5QuotientSeries).sum
      (complexSeries pureB5QuotientSeries) 0 4 :=
    ((complexSeries pureB5QuotientSeries).hasFPowerSeriesOnBall
      (lt_of_lt_of_le (by norm_num) le_radius_complexSeries_pureB5QuotientSeries)).mono
      (by norm_num) le_radius_complexSeries_pureB5QuotientSeries
  simpa only [pureB5, pureB5Series, Polynomial.coe_X, Polynomial.aeval_X] using
    sum_polynomial_mul (hasSum_of_hasFPowerSeriesOnBall hq (mem_radius_four_ball hz))
      Polynomial.X

private theorem pos_radius_X_mul_pureJSeries :
    0 < (complexSeries (PowerSeries.X * pureJSeries)).radius := by
  apply lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1)
  apply (complexSeries (PowerSeries.X * pureJSeries)).le_radius_of_bound (r := (1 : ℝ≥0)) 2
  intro n
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    NNReal.coe_one, one_pow, mul_one]
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, coeff_pureJSeries, Complex.norm_ratCast]
    exact_mod_cast abs_pureJCoeff_le n

private theorem weighted_pureJ_trace :
    (fun z : ℂ => (mobiusCoordinate z - 2) * pureB5 (mobiusCoordinate z)) =ᶠ[𝓝 0]
      (fun z => z * pureJ z + mobiusAnalyticInvolution z * pureJ (mobiusAnalyticInvolution z)) := by
  have h := symmetrizedAnalytic_pullback_of_pos_radius
    (PowerSeries.X * pureJSeries) pos_radius_X_mul_pureJSeries
  have hyc : ContinuousAt mobiusCoordinate 0 :=
    (analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1)).continuousAt
  have hwc : ContinuousAt mobiusAnalyticInvolution 0 :=
    (analyticAt_mobiusAnalyticInvolution (by norm_num : (0 : ℂ) ≠ 1)).continuousAt
  have hx : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 :=
    continuousAt_id.norm.eventually_lt_const (by norm_num)
  have hw : ∀ᶠ z : ℂ in 𝓝 0, ‖mobiusAnalyticInvolution z‖ < 1 :=
    hwc.norm.eventually_lt_const (by norm_num [mobiusAnalyticInvolution])
  have hy : ∀ᶠ z : ℂ in 𝓝 0, ‖mobiusCoordinate z‖ < 4 :=
    hyc.norm.eventually_lt_const (by norm_num [mobiusCoordinate])
  filter_upwards [h, hx, hw, hy] with z hz hzx hzw hzy
  have hj (t : ℂ) (ht : ‖t‖ < 1) :
      (complexSeries (PowerSeries.X * pureJSeries)).sum t = t * pureJ t := by
    simpa only [Polynomial.coe_X, Polynomial.aeval_X] using sum_polynomial_mul
      (hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_pureJ (by
        simpa only [EMetric.mem_ball, edist_zero_right, ← ofReal_norm_eq_enorm,
          ENNReal.ofReal_lt_one] using ht)) Polynomial.X
  have hb := sum_polynomial_mul
    (hasSum_of_hasFPowerSeriesOnBall hasFPowerSeriesOnBall_pureB5
      (mem_radius_four_ball hzy)) (Polynomial.X - Polynomial.C 2)
  simp only [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, map_sub, map_ofNat,
    Polynomial.aeval_X, Polynomial.aeval_C, Rat.cast_ofNat] at hb
  have htwo : ((2 : Polynomial ℚ) : PowerSeries ℚ) = 2 :=
    map_ofNat (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) 2
  rw [htwo] at hb
  change (complexSeries (symmetrizedDescent (PowerSeries.X * pureJSeries))).sum
      (mobiusCoordinate z) = (complexSeries (PowerSeries.X * pureJSeries)).sum z +
        (complexSeries (PowerSeries.X * pureJSeries)).sum (mobiusAnalyticInvolution z) at hz
  rw [symmetrizedDescent_X_mul_pureJSeries, hb, hj z hzx,
    hj (mobiusAnalyticInvolution z) hzw] at hz
  exact hz

/-- The literal factorial formula for J holds as an analytic germ, including zero. -/
theorem pureJ_factorial_pullback :
    pureJ =ᶠ[𝓝 (0 : ℂ)] (fun z =>
      z * (complexSeries pureB5QuotientSeries).sum (mobiusCoordinate z)) := by
  have hyc : ContinuousAt mobiusCoordinate 0 :=
    (analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1)).continuousAt
  have hy : ∀ᶠ z : ℂ in 𝓝 0, ‖mobiusCoordinate z‖ < 4 :=
    hyc.norm.eventually_lt_const (by norm_num [mobiusCoordinate])
  have hne : ∀ᶠ z : ℂ in 𝓝 0, z ≠ 1 ∧ z ≠ 2 :=
    (eventually_ne_nhds (by norm_num)).and (eventually_ne_nhds (by norm_num))
  filter_upwards [pureB5_pullback, weighted_pureJ_trace, hy, hne] with z h0 h1 hzy hz
  by_cases hz0 : z = 0
  · simp [hz0]
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz.1
  have hz2 : z - 2 ≠ 0 := sub_ne_zero.mpr hz.2
  have hw : (z - 1) * mobiusAnalyticInvolution z = z := by
    simp only [mobiusAnalyticInvolution]
    field_simp
  have hcoord : (z - 1) * mobiusCoordinate z = z ^ 2 := by
    change (z - 1) * (z + mobiusAnalyticInvolution z) = z ^ 2
    linear_combination hw
  have hclear : z * pureJ z = (z - 1) * pureB5 (mobiusCoordinate z) := by
    apply mul_left_cancel₀ hz2
    change (z - 2) * (z * pureJ z) = (z - 2) * ((z - 1) * pureB5 (mobiusCoordinate z))
    change (z + mobiusAnalyticInvolution z - 2) * pureB5 (mobiusCoordinate z) = _ at h1
    linear_combination (z - 1) * mobiusAnalyticInvolution z * h0 - (z - 1) * h1 +
      pureJ z * hw
  rw [pureB5_eq_mul_quotient hzy] at hclear
  apply mul_left_cancel₀ hz0
  linear_combination hclear + (complexSeries pureB5QuotientSeries).sum (mobiusCoordinate z) * hcoord

end DirichletL
