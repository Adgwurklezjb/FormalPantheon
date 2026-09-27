import Analysis.QProductEvaluation
import Analysis.ThetaProducts
import Analysis.ThetaAnalytic

/-!
Complex theta product identities on the open unit disk, obtained by
evaluating Lau-Lee-Ono v3 Theorem 4.1.4 and extending analytically.
These are inputs to the eta identities in CDT v2 Section 11.1.
-/

namespace DirichletL

open Filter
open scoped Topology

private theorem theta_product_eqOn_unitDisk {f g : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hf : HasFPowerSeriesOnBall f p 0 1)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hfg : ∀ q : ℂ, ‖q‖ < 1 / 4 → f q = g q) {q : ℂ} (hq : ‖q‖ < 1) :
    f q = g q := by
  have hf' : AnalyticOnNhd ℂ f (Metric.ball 0 1) := by
    simpa only [← ENNReal.ofReal_one, Metric.emetric_ball] using hf.analyticOnNhd
  have hg' := (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mpr hg
  apply hf'.eqOn_of_preconnected_of_eventuallyEq hg'
    (convex_ball (0 : ℂ) 1).isPreconnected (by simp : (0 : ℂ) ∈ Metric.ball 0 1) _
    (by simpa using hq)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)] with z hz
  exact hfg z (by simpa using hz)

private theorem thetaTwoNormalizedSeries_eq_positive_formalProduct :
    thetaTwoNormalizedSeries =
      2 * (formalProduct (fun i => 1 - PowerSeries.X ^ (2 * (i + 1))) *
        formalProduct (fun i => 1 + PowerSeries.X ^ (2 * (i + 1))) ^ 2) := by
  have ht : formalProduct (fun i => 1 + (PowerSeries.X : PowerSeries ℤ) ^ (2 * i)) =
      2 * formalProduct (fun i => 1 + PowerSeries.X ^ (2 * (i + 1))) := by
    have h := formalProduct_eq_mul_tail (f := fun i =>
      1 + (PowerSeries.X : PowerSeries ℤ) ^ (2 * i)) (fun i => by
        rw [add_sub_cancel_left]
        exact pow_dvd_pow PowerSeries.X (by omega))
    simpa only [mul_zero, pow_zero, one_add_one_eq_two] using h
  rw [thetaTwoNormalizedSeries_eq_formalProduct, ht]
  ring

theorem sum_complexSeries_thetaThreeSeries_eq_tprod {q : ℂ} (hq : ‖q‖ < 1) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q =
      (∏' i : ℕ, (1 - q ^ (2 * (i + 1)))) * (∏' i : ℕ, (1 + q ^ (2 * i + 1))) ^ 2 := by
  apply theta_product_eqOn_unitDisk hasFPowerSeriesOnBall_thetaThreeSeries _ _ hq
  · simpa only [neg_one_mul, sub_eq_add_neg, one_mul] using
      (differentiableOn_tprod_one_add_mul_pow (s := -1) (by norm_num)
        (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega)).mul
        ((differentiableOn_tprod_one_add_mul_pow (s := 1) (by norm_num)
          (e := fun i => 2 * i + 1) (by intro i; dsimp only; omega)).pow 2)
  · intro z hz
    have hm := hasSum_formalProduct_one_add_C_mul_X_pow (c := -1) (by norm_num)
      (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega) hz
    have hp := hasSum_formalProduct_one_add_C_mul_X_pow (c := 1) (by norm_num)
      (e := fun i => 2 * i + 1) (by intro i; dsimp only; omega) hz
    apply sum_complexSeries_eq_of_hasSum
    simpa only [thetaThreeSeries_eq_formalProduct, map_mul, map_pow, pow_two,
      map_neg, map_one, Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg, one_mul] using
      hasSum_powerSeries_mul hm (hasSum_powerSeries_mul hp hp)

theorem sum_complexSeries_thetaFourSeries_eq_tprod {q : ℂ} (hq : ‖q‖ < 1) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q =
      (∏' i : ℕ, (1 - q ^ (2 * (i + 1)))) * (∏' i : ℕ, (1 - q ^ (2 * i + 1))) ^ 2 := by
  apply theta_product_eqOn_unitDisk hasFPowerSeriesOnBall_thetaFourSeries _ _ hq
  · simpa only [neg_one_mul, sub_eq_add_neg] using
      (differentiableOn_tprod_one_add_mul_pow (s := -1) (by norm_num)
        (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega)).mul
        ((differentiableOn_tprod_one_add_mul_pow (s := -1) (by norm_num)
          (e := fun i => 2 * i + 1) (by intro i; dsimp only; omega)).pow 2)
  · intro z hz
    have hm := hasSum_formalProduct_one_add_C_mul_X_pow (c := -1) (by norm_num)
      (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega) hz
    have ho := hasSum_formalProduct_one_add_C_mul_X_pow (c := -1) (by norm_num)
      (e := fun i => 2 * i + 1) (by intro i; dsimp only; omega) hz
    apply sum_complexSeries_eq_of_hasSum
    simpa only [thetaFourSeries_eq_formalProduct, map_mul, map_pow, pow_two,
      map_neg, map_one, Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg] using
      hasSum_powerSeries_mul hm (hasSum_powerSeries_mul ho ho)

theorem sum_complexSeries_thetaTwoNormalizedSeries_eq_tprod {q : ℂ} (hq : ‖q‖ < 1) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum q =
      2 * ((∏' i : ℕ, (1 - q ^ (2 * (i + 1)))) *
        (∏' i : ℕ, (1 + q ^ (2 * (i + 1)))) ^ 2) := by
  apply theta_product_eqOn_unitDisk hasFPowerSeriesOnBall_thetaTwoNormalizedSeries _ _ hq
  · simpa only [neg_one_mul, sub_eq_add_neg, one_mul] using (differentiableOn_const 2).mul
      ((differentiableOn_tprod_one_add_mul_pow (s := -1) (by norm_num)
        (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega)).mul
        ((differentiableOn_tprod_one_add_mul_pow (s := 1) (by norm_num)
          (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega)).pow 2))
  · intro z hz
    have hm := hasSum_formalProduct_one_add_C_mul_X_pow (c := -1) (by norm_num)
      (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega) hz
    have hp := hasSum_formalProduct_one_add_C_mul_X_pow (c := 1) (by norm_num)
      (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega) hz
    have hh := hasSum_polynomial_mul (hasSum_powerSeries_mul hm (hasSum_powerSeries_mul hp hp))
      (Polynomial.C 2)
    have htwo : ((Polynomial.C (2 : ℚ) : Polynomial ℚ) : PowerSeries ℚ) = 2 := by
      rw [Polynomial.coe_C, map_ofNat]
    rw [htwo] at hh
    apply sum_complexSeries_eq_of_hasSum
    simpa [thetaTwoNormalizedSeries_eq_positive_formalProduct, map_ofNat, pow_two,
      sub_eq_add_neg] using hh

theorem sum_complexSeries_thetaThreeSeries_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q ≠ 0 := by
  rw [sum_complexSeries_thetaThreeSeries_eq_tprod hq]
  apply mul_ne_zero
  · simpa only [neg_one_mul, sub_eq_add_neg] using
      tprod_one_add_mul_pow_ne_zero (s := -1) (by norm_num)
        (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega) hq
  · apply pow_ne_zero
    simpa only [one_mul] using tprod_one_add_mul_pow_ne_zero (s := 1) (by norm_num)
      (e := fun i => 2 * i + 1) (by intro i; dsimp only; omega) hq

theorem sum_complexSeries_thetaFourSeries_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q ≠ 0 := by
  rw [sum_complexSeries_thetaFourSeries_eq_tprod hq]
  apply mul_ne_zero
  · simpa only [neg_one_mul, sub_eq_add_neg] using
      tprod_one_add_mul_pow_ne_zero (s := -1) (by norm_num)
        (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega) hq
  · apply pow_ne_zero
    simpa only [neg_one_mul, sub_eq_add_neg] using
      tprod_one_add_mul_pow_ne_zero (s := -1) (by norm_num)
        (e := fun i => 2 * i + 1) (by intro i; dsimp only; omega) hq

theorem sum_complexSeries_thetaTwoNormalizedSeries_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum q ≠ 0 := by
  rw [sum_complexSeries_thetaTwoNormalizedSeries_eq_tprod hq]
  apply mul_ne_zero (by norm_num)
  apply mul_ne_zero
  · simpa only [neg_one_mul, sub_eq_add_neg] using
      tprod_one_add_mul_pow_ne_zero (s := -1) (by norm_num)
        (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega) hq
  · apply pow_ne_zero
    simpa only [one_mul] using tprod_one_add_mul_pow_ne_zero (s := 1) (by norm_num)
      (e := fun i => 2 * (i + 1)) (by intro i; dsimp only; omega) hq

end DirichletL
