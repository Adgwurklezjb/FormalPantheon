import Analysis.QEulerProduct
import Analysis.ThetaProductAnalytic

/-!
The product of the three theta constants, with the normalized theta-two
factor, as an Euler-product cube. This combines the analytic forms of
Lau-Lee-Ono v3 Theorem 4.1.4 for the eta normalization in DLMF 27.14.12.
-/

namespace DirichletL

private theorem theta_auxiliary_product_eq_one {q : ℂ} (hq : ‖q‖ < 1) :
    (∏' i : ℕ, (1 - q ^ (2 * i + 1))) * (∏' i : ℕ, (1 + q ^ (2 * i + 1))) *
      (∏' i : ℕ, (1 + q ^ (2 * (i + 1)))) = 1 := by
  have hq2 : ‖q ^ 2‖ < 1 := by simpa only [norm_pow] using pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hab := tprod_one_sub_pow_mul_one_add_pow
    (e := fun i => 2 * i + 1) (by intro i; dsimp only; omega) hq
  have hbc := tprod_one_sub_pow_mul_one_add_pow
    (e := fun i => i + 1) (fun _ => le_rfl) hq2
  have hc : qEulerProduct (q ^ 2) * (∏' i : ℕ, (1 + q ^ (2 * (i + 1)))) =
      qEulerProduct ((q ^ 2) ^ 2) := by
    simpa only [qEulerProduct, pow_mul] using hbc
  have ha := tprod_odd_mul_qEulerProduct_sq hq2
  apply mul_right_cancel₀ (qEulerProduct_ne_zero hq2)
  rw [one_mul]
  calc
    _ = ((∏' i : ℕ, (1 - q ^ (2 * i + 1))) *
        (∏' i : ℕ, (1 + q ^ (2 * i + 1)))) *
        (qEulerProduct (q ^ 2) * (∏' i : ℕ, (1 + q ^ (2 * (i + 1))))) := by ring
    _ = qEulerProduct (q ^ 2) := by rw [hab, hc, ha]

theorem sum_complexSeries_theta_product_eq_qEulerProduct {q : ℂ} (hq : ‖q‖ < 1) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q *
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q *
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum q =
        2 * qEulerProduct (q ^ 2) ^ 3 := by
  rw [sum_complexSeries_thetaThreeSeries_eq_tprod hq,
    sum_complexSeries_thetaFourSeries_eq_tprod hq,
    sum_complexSeries_thetaTwoNormalizedSeries_eq_tprod hq]
  have he : (∏' i : ℕ, (1 - q ^ (2 * (i + 1)))) = qEulerProduct (q ^ 2) := by
    simp only [qEulerProduct, pow_mul]
  rw [he]
  calc
    _ = 2 * qEulerProduct (q ^ 2) ^ 3 *
        ((∏' i : ℕ, (1 - q ^ (2 * i + 1))) *
          (∏' i : ℕ, (1 + q ^ (2 * i + 1))) *
          (∏' i : ℕ, (1 + q ^ (2 * (i + 1))))) ^ 2 := by ring
    _ = _ := by rw [theta_auxiliary_product_eq_one hq]; ring

end DirichletL
