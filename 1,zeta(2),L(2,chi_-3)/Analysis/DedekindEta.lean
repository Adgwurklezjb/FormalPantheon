import Analysis.ThetaEulerProduct

/-!
Dedekind eta with the product normalization of DLMF 27.14.12-13.
The cubic theta identity retains the normalized theta-two constant 2.
This prepares the eta quotients underlying CDT v2 Section 11.1.
-/

namespace DirichletL

open Complex Function.Periodic
open scoped Real

/-- Dedekind eta with the exponential and positive-index product of DLMF 27.14.12. -/
noncomputable def dedekindEta (τ : ℂ) : ℂ :=
  exp (π * I * τ / 12) * qEulerProduct (qParam 1 τ)

theorem norm_qParam_one_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖qParam 1 τ‖ < 1 := by
  simpa using (norm_qParam_lt_iff (h := 1) (by norm_num) 0 τ).mpr hτ

theorem differentiableOn_dedekindEta :
    DifferentiableOn ℂ dedekindEta {τ : ℂ | 0 < τ.im} := by
  have hp : Differentiable ℂ (fun τ : ℂ => exp (π * I * τ / 12)) :=
    (((differentiable_const _).mul differentiable_id).div_const 12).cexp
  have hq : Differentiable ℂ (qParam 1) := by
    change Differentiable ℂ (fun τ : ℂ => exp (2 * π * I * τ / 1))
    exact (((differentiable_const _).mul differentiable_id).div_const 1).cexp
  apply hp.differentiableOn.mul
  apply differentiableOn_qEulerProduct.comp hq.differentiableOn
  intro τ hτ
  simpa using norm_qParam_one_lt_one hτ

theorem dedekindEta_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : dedekindEta τ ≠ 0 :=
  mul_ne_zero (exp_ne_zero _) (qEulerProduct_ne_zero (norm_qParam_one_lt_one hτ))

private theorem qParam_one_add_one (τ : ℂ) : qParam 1 (τ + 1) = qParam 1 τ := by
  simp only [qParam, ofReal_one, div_one]
  have he : 2 * π * I * (τ + 1) = 2 * π * I * τ + 2 * π * I := by ring
  rw [he, exp_add, exp_two_pi_mul_I, mul_one]

private theorem qParam_one_two_mul (τ : ℂ) : qParam 1 (2 * τ) = qParam 1 τ ^ 2 := by
  simp only [qParam, ofReal_one, div_one]
  rw [← exp_nat_mul]
  congr 1
  ring

theorem dedekindEta_add_one (τ : ℂ) :
    dedekindEta (τ + 1) = exp (π * I / 12) * dedekindEta τ := by
  simp only [dedekindEta, qParam_one_add_one]
  have he : π * I * (τ + 1) / 12 = π * I / 12 + π * I * τ / 12 := by ring
  rw [he, exp_add]
  ring

theorem dedekindEta_two_mul_pow_three {τ : ℂ} (hτ : 0 < τ.im) :
    dedekindEta (2 * τ) ^ 3 = exp (π * I * τ / 2) *
      ((complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum (qParam 1 τ) *
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum (qParam 1 τ) *
        (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaTwoNormalizedSeries)).sum
          (qParam 1 τ)) / 2 := by
  rw [dedekindEta, mul_pow, qParam_one_two_mul, ← exp_nat_mul,
    sum_complexSeries_theta_product_eq_qEulerProduct (norm_qParam_one_lt_one hτ)]
  have he : (3 : ℂ) * (π * I * (2 * τ) / 12) = π * I * τ / 2 := by ring
  norm_num only [Nat.cast_ofNat]
  rw [he]
  ring

end DirichletL
