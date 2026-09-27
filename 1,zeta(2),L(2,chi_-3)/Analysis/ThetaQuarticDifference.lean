import Analysis.ThetaTransformations
import Analysis.ThetaProductAnalytic

/-!
The normalized difference in DLMF 20.7.5 and its theta transformations,
preparing the local square at the CDT level-two quotient branch value 4.
Meanings and branch checks precede the bodies in
-/

namespace DirichletL

open Complex Function.Periodic
open scoped Real

/-- The difference in the quartic theta identity with the theta-two prefactor removed. -/
noncomputable def thetaQuarticDifference (q : ℂ) : ℂ :=
  (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q ^ 4 -
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q ^ 4 -
    q * (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum q ^ 4

theorem thetaQuarticDifference_zero : thetaQuarticDifference 0 = 0 := by
  have hq : ‖(0 : ℂ)‖ < 1 := by norm_num
  rw [thetaQuarticDifference, sum_complexSeries_thetaThreeSeries_eq_tprod hq,
    sum_complexSeries_thetaFourSeries_eq_tprod hq]
  simp [pow_mul]

theorem analyticOnNhd_thetaQuarticDifference :
    AnalyticOnNhd ℂ thetaQuarticDifference (Metric.ball 0 1) := by
  have h3 : AnalyticOnNhd ℂ
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum
      (Metric.ball 0 1) := by
    simpa only [← ENNReal.ofReal_one, Metric.emetric_ball] using
      hasFPowerSeriesOnBall_thetaThreeSeries.analyticOnNhd
  have h4 : AnalyticOnNhd ℂ
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum
      (Metric.ball 0 1) := by
    simpa only [← ENNReal.ofReal_one, Metric.emetric_ball] using
      hasFPowerSeriesOnBall_thetaFourSeries.analyticOnNhd
  have h2 : AnalyticOnNhd ℂ
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum
      (Metric.ball 0 1) := by
    simpa only [← ENNReal.ofReal_one, Metric.emetric_ball] using
      hasFPowerSeriesOnBall_thetaTwoNormalizedSeries.analyticOnNhd
  intro q hq
  exact (((h3 q hq).pow 4).sub ((h4 q hq).pow 4)).sub
    (analyticAt_id.mul ((h2 q hq).pow 4))

theorem thetaQuarticDifference_add_half {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQuarticDifference (Function.Periodic.qParam 1 (τ + 1 / 2)) =
      -thetaQuarticDifference (Function.Periodic.qParam 1 τ) := by
  have hq : qParam 1 (τ + 1 / 2) = -qParam 1 τ := by
    simp only [qParam, ofReal_one, div_one]
    rw [show 2 * π * I * (τ + 1 / 2) = 2 * π * I * τ + π * I by ring,
      exp_add, exp_pi_mul_I, mul_neg_one]
  unfold thetaQuarticDifference
  rw [sum_complexSeries_thetaThreeSeries_add_half hτ,
    sum_complexSeries_thetaFourSeries_add_half hτ,
    sum_complexSeries_thetaTwoNormalizedSeries_add_half hτ, hq]
  ring

theorem thetaQuarticDifference_inversion {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQuarticDifference (Function.Periodic.qParam 1 (-1 / (4 * τ))) =
      -4 * τ ^ 2 * thetaQuarticDifference (Function.Periodic.qParam 1 τ) := by
  have hτ0 : τ ≠ 0 := fun h => (ne_of_gt hτ) (congrArg Complex.im h)
  let s : ℂ := (-I * (2 * τ)) ^ (1 / 2 : ℂ)
  have hs0 : s ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl
      (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (mul_ne_zero (by norm_num) hτ0)))
  have hs2 : s ^ 2 = -I * (2 * τ) := by
    simpa only [s, one_div] using cpow_nat_inv_pow (-I * (2 * τ)) (n := 2) two_ne_zero
  have hs4 : s ^ 4 = -4 * τ ^ 2 := by
    calc
      _ = (s ^ 2) ^ 2 := by ring
      _ = (-I * (2 * τ)) ^ 2 := by rw [hs2]
      _ = -4 * τ ^ 2 := by rw [mul_pow, neg_sq, I_sq]; ring
  have he4 : exp (-π * I / (8 * τ)) ^ 4 = qParam 1 (-1 / (4 * τ)) := by
    rw [← exp_nat_mul]
    simp only [qParam, ofReal_one, div_one, Nat.cast_ofNat]
    congr 1
    field_simp
    ring
  have he2 : exp (-π * I * τ / 2) ^ 4 = (qParam 1 τ)⁻¹ := by
    rw [← exp_nat_mul]
    simp only [qParam, ofReal_one, div_one, Nat.cast_ofNat]
    rw [← exp_neg]
    congr 1
    ring
  have h3 := sum_complexSeries_thetaThreeSeries_inversion hτ
  have h4 := sum_complexSeries_thetaFourSeries_inversion hτ
  have h2 := sum_complexSeries_thetaTwoNormalizedSeries_inversion hτ
  have hq0 : qParam 1 τ ≠ 0 := exp_ne_zero _
  have heq : s ^ 4 * thetaQuarticDifference (qParam 1 τ) =
      thetaQuarticDifference (qParam 1 (-1 / (4 * τ))) := by
    dsimp only [thetaQuarticDifference]
    rw [h3, h4, h2]
    simp only [mul_pow, div_pow, one_pow, he4, he2]
    change s ^ 4 * ((1 / s ^ 4) *
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum
        (qParam 1 (-1 / (4 * τ))) ^ 4 -
      (1 / s ^ 4) * qParam 1 (-1 / (4 * τ)) *
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum
          (qParam 1 (-1 / (4 * τ))) ^ 4 -
      qParam 1 τ * ((1 / s ^ 4) * (qParam 1 τ)⁻¹ *
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum
          (qParam 1 (-1 / (4 * τ))) ^ 4)) = _
    field_simp [hs0, hq0]
    ring
  rw [hs4] at heq
  exact heq.symm

end DirichletL
