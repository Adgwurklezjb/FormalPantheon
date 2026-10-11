import Analysis.LevelTwoSquare
import Analysis.ThetaTransformations
import Analysis.MobiusAnalyticInvolution

/-!
The original-coordinate theta quotient and its sheet symmetry.
Source: CDT v2 TeX 6947-6958 and 7157-7173; DLMF 20.7.5.
-/

namespace DirichletL

open scoped Topology

/-- The original x coordinate, with theta nome q and quotient nome q squared. -/
noncomputable def levelTwoLambda (q : ℂ) : ℂ :=
  1 - (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q ^ 4 /
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q ^ 4

theorem analyticOnNhd_levelTwoLambda :
    AnalyticOnNhd ℂ levelTwoLambda (Metric.ball 0 1) := by
  have hA : AnalyticOnNhd ℂ
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum
      (Metric.ball 0 1) := by
    simpa only [← ENNReal.ofReal_one, Metric.emetric_ball] using
      hasFPowerSeriesOnBall_thetaThreeSeries.analyticOnNhd
  have hB : AnalyticOnNhd ℂ
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum
      (Metric.ball 0 1) := by
    simpa only [← ENNReal.ofReal_one, Metric.emetric_ball] using
      hasFPowerSeriesOnBall_thetaFourSeries.analyticOnNhd
  intro q hq
  exact analyticAt_const.sub (((hB q hq).pow 4).div ((hA q hq).pow 4)
    (pow_ne_zero 4 (sum_complexSeries_thetaThreeSeries_ne_zero (by simpa using hq))))

theorem levelTwoLambda_zero : levelTwoLambda 0 = 0 := by
  have hq : ‖(0 : ℂ)‖ < 1 := by norm_num
  rw [levelTwoLambda, sum_complexSeries_thetaThreeSeries_eq_tprod hq,
    sum_complexSeries_thetaFourSeries_eq_tprod hq]
  simp [pow_mul]

theorem levelTwoLambda_ne_one {q : ℂ} (hq : ‖q‖ < 1) :
    levelTwoLambda q ≠ 1 := by
  have hA := sum_complexSeries_thetaThreeSeries_ne_zero hq
  have hB := sum_complexSeries_thetaFourSeries_ne_zero hq
  intro he
  apply div_ne_zero (pow_ne_zero 4 hB) (pow_ne_zero 4 hA)
  dsimp only [levelTwoLambda] at he
  linear_combination -he

private theorem sum_complexSeries_thetaThreeSeries_neg {q : ℂ} (hq : ‖q‖ < 1) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum (-q) =
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q := by
  by_cases hq0 : q = 0
  · subst q
    simp only [neg_zero]
    rw [sum_complexSeries_thetaThreeSeries_eq_tprod hq,
      sum_complexSeries_thetaFourSeries_eq_tprod hq]
    simp [pow_mul]
  · let τ := Function.Periodic.invQParam 1 q
    have hτ : 0 < τ.im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0
    have hqτ : Function.Periodic.qParam 1 τ = q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    have hshift : Function.Periodic.qParam 1 (τ + 1 / 2) =
        -Function.Periodic.qParam 1 τ := by
      simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (τ + 1 / 2) =
        2 * (Real.pi : ℂ) * Complex.I * τ + (Real.pi : ℂ) * Complex.I by ring,
        Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
    have h := sum_complexSeries_thetaThreeSeries_add_half hτ
    rwa [hshift, hqτ] at h

theorem levelTwoLambda_neg {q : ℂ} (hq : ‖q‖ < 1) :
    levelTwoLambda (-q) = mobiusAnalyticInvolution (levelTwoLambda q) := by
  let A := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q
  let B := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q
  have hA : A ≠ 0 := sum_complexSeries_thetaThreeSeries_ne_zero hq
  have hB : B ≠ 0 := sum_complexSeries_thetaFourSeries_ne_zero hq
  have hBneg :
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum (-q) = A := by
    have h := sum_complexSeries_thetaThreeSeries_neg (q := -q) (by simpa using hq)
    simpa only [neg_neg] using h.symm
  rw [levelTwoLambda, hBneg, sum_complexSeries_thetaThreeSeries_neg hq]
  change 1 - A ^ 4 / B ^ 4 = (1 - B ^ 4 / A ^ 4) / ((1 - B ^ 4 / A ^ 4) - 1)
  rw [show (1 - B ^ 4 / A ^ 4) - 1 = -B ^ 4 / A ^ 4 by ring, div_div_eq_mul_div]
  field_simp [hA, hB]
  ring

theorem mobiusCoordinate_levelTwoLambda {q : ℂ} (hq : ‖q‖ < 1) :
    mobiusCoordinate (levelTwoLambda q) = levelTwoHauptmodul (q ^ 2) := by
  let A := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q
  let B := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q
  let C := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum q
  have hA : A ≠ 0 := sum_complexSeries_thetaThreeSeries_ne_zero hq
  have hB : B ≠ 0 := sum_complexSeries_thetaFourSeries_ne_zero hq
  have hquartic : A ^ 4 - B ^ 4 = q * C ^ 4 := sum_complexSeries_theta_quartic hq
  have hnum : q ^ 2 * C ^ 8 = (A ^ 4 - B ^ 4) ^ 2 := by rw [hquartic]; ring
  rw [levelTwoHauptmodul_sq_eq_theta_quotient hq]
  change (1 - B ^ 4 / A ^ 4) + (1 - B ^ 4 / A ^ 4) / ((1 - B ^ 4 / A ^ 4) - 1) =
    -(q ^ 2 * C ^ 8) / (A ^ 4 * B ^ 4)
  rw [hnum, show (1 - B ^ 4 / A ^ 4) - 1 = -B ^ 4 / A ^ 4 by ring, div_div_eq_mul_div]
  field_simp [hA, hB]
  ring

end DirichletL
