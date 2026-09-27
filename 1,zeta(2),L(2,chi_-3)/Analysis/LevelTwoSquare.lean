import Analysis.LevelTwoHauptmodul
import Analysis.ThetaEulerProduct
import Analysis.ThetaQuarticIdentity

/-!
The theta square underlying the branch value 4 of CDT's level-two quotient,
from DLMF 20.7.5 and CDT v2 TeX 6947-6958 and 7176-7197.
Meanings and nonzero denominators precede the bodies in
-/

namespace DirichletL

theorem levelTwoHauptmodul_sq_eq_theta_quotient {q : ℂ} (hq : ‖q‖ < 1) :
    levelTwoHauptmodul (q ^ 2) =
      -(q ^ 2 *
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum q ^ 8) /
        ((complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q ^ 4 *
          (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q ^ 4) := by
  let A := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q
  let B := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q
  let C := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum q
  let E := qEulerProduct (q ^ 2)
  let P := ∏' n : ℕ, (1 + (q ^ 2) ^ (n + 1))
  have hA : A ≠ 0 := sum_complexSeries_thetaThreeSeries_ne_zero hq
  have hB : B ≠ 0 := sum_complexSeries_thetaFourSeries_ne_zero hq
  have hC0 : C ≠ 0 := sum_complexSeries_thetaTwoNormalizedSeries_ne_zero hq
  have hABC : A * B * C = 2 * E ^ 3 :=
    sum_complexSeries_theta_product_eq_qEulerProduct hq
  have hC : C = 2 * (E * P ^ 2) := by
    simpa only [C, E, P, qEulerProduct, pow_mul] using
      sum_complexSeries_thetaTwoNormalizedSeries_eq_tprod hq
  have hratio : C ^ 8 / (A ^ 4 * B ^ 4) = 256 * P ^ 24 := by
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero 4 hA) (pow_ne_zero 4 hB))).mpr
    apply mul_right_cancel₀ (pow_ne_zero 4 hC0)
    calc
      C ^ 8 * C ^ 4 = C ^ 12 := by ring
      _ = (2 * (E * P ^ 2)) ^ 12 := by rw [hC]
      _ = 256 * P ^ 24 * (2 * E ^ 3) ^ 4 := by ring
      _ = (256 * P ^ 24 * (A ^ 4 * B ^ 4)) * C ^ 4 := by rw [← hABC]; ring
  change -256 * q ^ 2 * P ^ 24 = -(q ^ 2 * C ^ 8) / (A ^ 4 * B ^ 4)
  rw [show -(q ^ 2 * C ^ 8) / (A ^ 4 * B ^ 4) =
    -q ^ 2 * (C ^ 8 / (A ^ 4 * B ^ 4)) by ring, hratio]
  ring

theorem one_sub_levelTwoHauptmodul_sq_div_four_eq_square {q : ℂ} (hq : ‖q‖ < 1) :
    1 - levelTwoHauptmodul (q ^ 2) / 4 =
      (((complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q ^ 4 +
          (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q ^ 4) /
        (2 * (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q ^ 2 *
          (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q ^ 2)) ^ 2 := by
  let A := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q
  let B := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q
  let C := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum q
  have hA : A ≠ 0 := sum_complexSeries_thetaThreeSeries_ne_zero hq
  have hB : B ≠ 0 := sum_complexSeries_thetaFourSeries_ne_zero hq
  have hquartic : A ^ 4 - B ^ 4 = q * C ^ 4 := sum_complexSeries_theta_quartic hq
  have hnum : q ^ 2 * C ^ 8 = (A ^ 4 - B ^ 4) ^ 2 := by rw [hquartic]; ring
  rw [levelTwoHauptmodul_sq_eq_theta_quotient hq]
  change 1 - (-(q ^ 2 * C ^ 8) / (A ^ 4 * B ^ 4)) / 4 =
    ((A ^ 4 + B ^ 4) / (2 * A ^ 2 * B ^ 2)) ^ 2
  rw [hnum]
  field_simp [hA, hB]
  ring

end DirichletL
