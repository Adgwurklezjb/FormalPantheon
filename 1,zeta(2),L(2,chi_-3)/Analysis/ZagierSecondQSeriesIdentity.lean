import Analysis.ZagierSecondModularIdentity
import Analysis.ZagierQSeriesTransfer

/-!
The integral formal second case-C identity from Zagier (2009), Section 5,
equation (7). The inverse q-coordinate and analytic uniqueness transfer the
proved modular identity to all coefficients. The preparation is recorded in
-/

namespace DirichletL

open Complex Filter Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped Topology ModularForm

theorem zagierSecondClearedAnalytic_zero : zagierSecondClearedAnalytic 0 = 0 := by
  simp [zagierSecondClearedAnalytic, zagierClearAAnalytic, zagierClearBAnalytic,
    zagierClearPolynomialAnalytic, zagierThetaAnalytic, hauptmodulProduct]

theorem zagierSecondClearedAnalytic_eventually_eq_zero :
    zagierSecondClearedAnalytic =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
  have hN := hasFPowerSeriesAt_zagierCaseCNAnalytic
  have hD := hasFPowerSeriesAt_zagierCaseCDAnalytic
  have hA := hasFPowerSeriesAt_zagierClearAAnalytic
  have hN0 : zagierCaseCNAnalytic 0 ≠ 0 := by
    simp [zagierCaseCNAnalytic, qEulerProduct_zero]
  have hD0 : zagierCaseCDAnalytic 0 ≠ 0 := by
    simp [zagierCaseCDAnalytic, qEulerProduct_zero]
  filter_upwards [hN.analyticAt.eventually_analyticAt, hD.analyticAt.eventually_analyticAt,
    hA.analyticAt.eventually_analyticAt, hN.continuousAt.eventually_ne hN0,
    hD.continuousAt.eventually_ne hD0, Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)]
    with q hn hd ha hn0 hd0 hq
  by_cases hq0 : q = 0
  · simpa only [hq0] using zagierSecondClearedAnalytic_zero
  have hq1 : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  let τ : ℍ := ⟨invQParam 1 q, invQParam_one_im_pos hq0 hq1⟩
  have hqp : qParam 1 (τ : ℂ) = q := qParam_right_inv (by norm_num) hq0
  have he := zagierSecondDerivativeDifferenceForm_eq_product τ
    (by simpa only [hqp] using hn) (by simpa only [hqp] using hd)
    (by simpa only [hqp] using ha) (by simpa only [hqp] using hn0)
    (by simpa only [hqp] using hd0)
  have hz : zagierSecondDerivativeDifferenceForm τ = 0 :=
    congrArg (fun f : ModularForm (CongruenceSubgroup.Gamma0 6) 4 => f τ)
      zagierSecondDerivativeDifferenceForm_eq_zero
  have hp : zagierSecondDerivativeDifferenceProduct q = 0 := by
    rw [← hqp, ← he, hz]
  exact (div_eq_zero_iff.mp hp).resolve_right
    (mul_ne_zero (pow_ne_zero 2 hn0) (pow_ne_zero 2 hd0))

theorem zagierSecondClearedSeries_eq_zero : zagierSecondClearedSeries = 0 := by
  have h := hasFPowerSeriesAt_zagierSecondClearedAnalytic.eq_zero_of_eventually
    zagierSecondClearedAnalytic_eventually_eq_zero
  ext n
  have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) h
  dsimp only at hn
  have hz : (0 : FormalMultilinearSeries ℂ ℂ ℂ).coeff n = 0 := by
    simp [FormalMultilinearSeries.coeff]
  rw [hz] at hn
  have hc : (PowerSeries.coeff (R := ℤ) n zagierSecondClearedSeries : ℂ) = 0 := by
    simpa [coeff_complexSeries, PowerSeries.coeff_map] using hn
  have hi : PowerSeries.coeff (R := ℤ) n zagierSecondClearedSeries = 0 := by exact_mod_cast hc
  simpa only [map_zero] using hi

theorem zagier_second_formal_identity :
    3 * zagierClearA ^ 2 - 2 * zagierCaseCN * zagierClearB =
      zagierClearPolynomial * zagierCaseCN ^ 4 := by
  exact sub_eq_zero.mp zagierSecondClearedSeries_eq_zero

end DirichletL
