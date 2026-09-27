import Analysis.PureFunctionDifferential
import Analysis.PureFunctionDescent
import Analysis.JFunctionDescent

/-!
The analytic differential system of CDT v2, equation `diffformulas`
(supplied TeX lines 7975-7982). Formal coefficient identities evaluate
on full neighborhoods of zero, before dividing by the singular leading factors.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

private theorem hasSum_pure_polynomial (p : ℚ[X]) (z : ℂ) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (p : PowerSeries ℚ) : ℂ) * z ^ n)
      (aeval z p) := by
  have h1 : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (1 : PowerSeries ℚ) : ℂ) * z ^ n)
      (1 : ℂ) := by
    convert hasSum_ite_eq (0 : ℕ) (1 : ℂ) using 1
    ext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  simpa only [mul_one] using hasSum_polynomial_mul h1 p

private theorem pure_first_order_analytic {F G : PowerSeries ℚ} {f g : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (complexSeries F) 0)
    (hg : HasFPowerSeriesAt g (complexSeries G) 0) (p q r s : ℚ[X])
    (he : (p : PowerSeries ℚ) * F.derivativeFun =
      (q : PowerSeries ℚ) * F + (r : PowerSeries ℚ) * G + (s : PowerSeries ℚ)) :
    ∀ᶠ z : ℂ in 𝓝 0,
      aeval z p * deriv f z = aeval z q * f z + aeval z r * g z + aeval z s := by
  obtain ⟨ρ, hρ⟩ := hf
  have hd := (hasFPowerSeriesOnBall_derivativeFun hρ).hasFPowerSeriesAt
  filter_upwards [eventually_hasSum_of_hasFPowerSeriesAt hρ.hasFPowerSeriesAt,
    eventually_hasSum_of_hasFPowerSeriesAt hg,
    eventually_hasSum_of_hasFPowerSeriesAt hd] with z hfz hgz hdz
  have hl := hasSum_polynomial_mul hdz p
  have hr := ((hasSum_polynomial_mul hfz q).add
    (hasSum_polynomial_mul hgz r)).add (hasSum_pure_polynomial s z)
  have hr' : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      ((q : PowerSeries ℚ) * F + (r : PowerSeries ℚ) * G + (s : PowerSeries ℚ)) : ℂ) * z ^ n)
      (aeval z q * f z + aeval z r * g z + aeval z s) := by
    simpa only [map_add, Rat.cast_add, add_mul] using hr
  rw [he] at hl
  exact hl.unique hr'

theorem pureB2_ode : ∀ᶠ z : ℂ in 𝓝 0,
    z * (4 - z) * deriv pureB2 z = (2 - z) * pureB2 z + z ^ 2 := by
  have h := pure_first_order_analytic hasFPowerSeriesOnBall_pureB2.hasFPowerSeriesAt
    hasFPowerSeriesOnBall_pureB3.hasFPowerSeriesAt
    (X * (C 4 - X)) (C 2 - X) 0 (X ^ 2) (by
      simpa only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_C, Polynomial.coe_X,
        Polynomial.coe_zero, Polynomial.coe_pow, Rat.cast_ofNat, zero_mul, add_zero] using
        pureB2Series_ode)
  simpa using h

theorem pureB3_ode : ∀ᶠ z : ℂ in 𝓝 0,
    z * (4 - z) * deriv pureB3 z = -pureB2 z + 2 * z := by
  have h2 : ((2 : ℚ[X]) : PowerSeries ℚ) = 2 :=
    map_ofNat (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) 2
  have h4 : ((4 : ℚ[X]) : PowerSeries ℚ) = 4 :=
    map_ofNat (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) 4
  have h := pure_first_order_analytic hasFPowerSeriesOnBall_pureB3.hasFPowerSeriesAt
    hasFPowerSeriesOnBall_pureB2.hasFPowerSeriesAt
    (X * (C 4 - X)) 0 (C (-1)) (C 2 * X) (by
      simpa only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_C, Polynomial.coe_X,
        Polynomial.coe_zero, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_one,
        map_ofNat, map_neg, map_one, h2, h4, Polynomial.coe_neg, Polynomial.coe_one,
        zero_mul, zero_add, neg_one_mul] using
        pureB3Series_first_order_ode)
  simpa using h

theorem pureB4_ode : ∀ᶠ z : ℂ in 𝓝 0,
    z * (4 - z) * deriv pureB4 z =
      (2 - z) * pureB4 z + (4 - z) * pureB2 z - 2 * z * (4 - z) := by
  have h := pure_first_order_analytic hasFPowerSeriesAt_pureB4
    hasFPowerSeriesOnBall_pureB2.hasFPowerSeriesAt
    (X * (C 4 - X)) (C 2 - X) (C 4 - X) (-(C 2 * X * (C 4 - X))) (by
      simpa only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_C, Polynomial.coe_X,
        Polynomial.coe_neg, Polynomial.coe_add, Rat.cast_ofNat, sub_eq_add_neg] using pureB4Series_ode)
  simpa [sub_eq_add_neg] using h

theorem pureB5_ode : ∀ᶠ z : ℂ in 𝓝 0,
    2 * z * (4 - z) * deriv pureB5 z = (4 - z) * pureB5 z - 2 * pureB2 z + 4 * z := by
  have h2 : ((2 : ℚ[X]) : PowerSeries ℚ) = 2 :=
    map_ofNat (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) 2
  have h4 : ((4 : ℚ[X]) : PowerSeries ℚ) = 4 :=
    map_ofNat (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) 4
  have h := pure_first_order_analytic hasFPowerSeriesOnBall_pureB5.hasFPowerSeriesAt
    hasFPowerSeriesOnBall_pureB2.hasFPowerSeriesAt
    (C 2 * X * (C 4 - X)) (C 4 - X) (C (-2)) (C 4 * X) (by
      simpa only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_C, Polynomial.coe_X,
        Polynomial.coe_add, Polynomial.coe_neg, Rat.cast_ofNat, Rat.cast_neg,
        map_ofNat, map_neg, h2, h4, neg_mul, sub_eq_add_neg] using pureB5Series_first_order_ode)
  simpa [sub_eq_add_neg] using h

end DirichletL
