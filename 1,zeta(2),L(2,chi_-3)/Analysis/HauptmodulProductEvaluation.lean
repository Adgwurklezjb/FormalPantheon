import Analysis.HauptmodulAnalytic
import Analysis.HauptmodulEulerProduct
import Analysis.HauptmodulModular
import Analysis.PowerSeriesCompositionAnalytic
import Analysis.QProductEvaluation

/-!
The convergent series and the Euler product for CDT v2 Section 11.1,
equation `haupt`, agree on the explicit disk of radius 1/2^25. The proof
clears the two nonvanishing Euler denominators and evaluates the exact
formal identity by absolutely convergent Cauchy multiplication.
-/

namespace DirichletL

open Function.Periodic UpperHalfPlane
open scoped Topology NNReal ENNReal

theorem hasSum_qEulerProductSeries {d : ℕ} (hd : 0 < d) {q : ℂ} (hq : ‖q‖ < 1 / 4) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) (qEulerProductSeries d)) : ℂ) * q ^ n)
        (qEulerProduct (q ^ d)) := by
  have he (i : ℕ) : i + 1 ≤ d * (i + 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (i + 1) (show 1 ≤ d by omega)
  simpa only [qEulerProductSeries, qEulerProduct, map_neg, map_one, neg_one_mul,
    Int.cast_neg, Int.cast_one, sub_eq_add_neg, pow_mul] using
      hasSum_formalProduct_one_add_C_mul_X_pow (c := -1) (by norm_num) he hq

theorem hasSum_hauptmodul {q : ℂ} (hq : ‖q‖ < 1 / 2 ^ 25) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) hauptmodul) : ℂ) * q ^ n)
        (hauptmodulAnalytic q) := by
  have hr : (0 : ℝ≥0∞) < 1 / 2 ^ 25 := by norm_num
  have hp := (FormalMultilinearSeries.hasFPowerSeriesOnBall _
    (hr.trans_le le_radius_complexSeries_hauptmodul)).mono hr
      le_radius_complexSeries_hauptmodul
  apply hasSum_of_hasFPowerSeriesOnBall hp
  apply mem_emetric_ball_zero_iff.mpr
  have hq' : ‖q‖₊ < (1 / 2 ^ 25 : ℝ≥0) := by exact_mod_cast hq
  simpa using ENNReal.coe_lt_coe.mpr hq'

theorem hauptmodulAnalytic_eq_product {q : ℂ} (hq : ‖q‖ < 1 / 2 ^ 25) :
    hauptmodulAnalytic q = hauptmodulProduct q := by
  have hq4 : ‖q‖ < 1 / 4 := hq.trans (by norm_num)
  have hq1 : ‖q‖ < 1 := by linarith
  have hX : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) PowerSeries.X) : ℂ) * q ^ n) q := by
    convert hasSum_ite_eq (1 : ℕ) q using 1
    ext n
    by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]
  have hleft := hasSum_powerSeries_mul
    (hasSum_powerSeries_mul (hasSum_hauptmodul hq)
      (hasSum_powerSeries_pow (hasSum_qEulerProductSeries (d := 2) (by norm_num) hq4) 8))
    (hasSum_powerSeries_pow (hasSum_qEulerProductSeries (d := 3) (by norm_num) hq4) 4)
  have hright := hasSum_powerSeries_mul
    (hasSum_powerSeries_mul hX
      (hasSum_powerSeries_pow (hasSum_qEulerProductSeries (d := 1) (by norm_num) hq4) 4))
    (hasSum_powerSeries_pow (hasSum_qEulerProductSeries (d := 6) (by norm_num) hq4) 8)
  have he := congrArg (PowerSeries.map (Int.castRingHom ℚ))
    hauptmodul_mul_qEulerProductSeries
  simp only [map_mul, map_pow] at he
  rw [he] at hleft
  have hv := hleft.unique hright
  have h2 : qEulerProduct (q ^ 2) ≠ 0 := by
    apply qEulerProduct_ne_zero
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq1 (by norm_num)
  have h3 : qEulerProduct (q ^ 3) ≠ 0 := by
    apply qEulerProduct_ne_zero
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq1 (by norm_num)
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero 8 h2) (pow_ne_zero 4 h3))).mpr
  simpa only [pow_one, mul_assoc] using hv

theorem hauptmodulAnalytic_qParam_eq_eta (τ : ℍ) (hq : ‖qParam 1 τ‖ < 1 / 2 ^ 25) :
    hauptmodulAnalytic (qParam 1 τ) = hauptmodulEta τ :=
  (hauptmodulAnalytic_eq_product hq).trans (hauptmodulEta_eq_product τ).symm

theorem hasFPowerSeriesAt_hauptmodulProduct :
    HasFPowerSeriesAt hauptmodulProduct
      (complexSeries (PowerSeries.map (Int.castRingHom ℚ) hauptmodul)) 0 := by
  apply hasFPowerSeriesAt_hauptmodulAnalytic.congr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2 ^ 25)]
    with q hq
  exact hauptmodulAnalytic_eq_product (by simpa using hq)

end DirichletL
