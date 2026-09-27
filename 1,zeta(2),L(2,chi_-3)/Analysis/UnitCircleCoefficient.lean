import Analysis.PowerSeriesAnalytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Exact unit-circle coefficient extraction for CDT v2, supplied TeX 4092-4130.
The Fourier sign and measure normalization are recorded before these proofs
-/

namespace DirichletL

open MeasureTheory
open scoped NNReal

local instance fact_two_pi_pos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

theorem circleMap_zero_one_eq_fourier (t : ℝ) :
    circleMap 0 1 t = fourier 1 (t : AddCircle (2 * Real.pi)) := by
  rw [fourier_coe_apply]
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul]
  congr 1
  push_cast
  field_simp [show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]

theorem fourier_neg_natCast_eq_inv_pow {T : ℝ} (n : ℕ) (t : AddCircle T) :
    fourier (-(n : ℤ)) t = (fourier 1 t)⁻¹ ^ n := by
  induction n with
  | zero => simp only [Nat.cast_zero, neg_zero, fourier_zero, pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, neg_add, fourier_add, ih, pow_succ]
    congr 1
    simp only [fourier_neg, fourier_one, ← Circle.coe_inv_eq_conj, Circle.coe_inv]

theorem coeff_eq_unitCircle_cauchyIntegral {p : PowerSeries ℂ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k p)) 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 1)) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n p = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∮ z in C(0, 1), z⁻¹ ^ n * (z⁻¹ * f z) := by
  have hc := hd.hasFPowerSeriesOnBall (show 0 < (1 : ℝ≥0) by norm_num)
  have heq := hf.eq_formalMultilinearSeries hc.hasFPowerSeriesAt
  have h := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n (fun _ => 1)) heq
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul,
    mul_one, cauchyPowerSeries_apply, sub_zero, one_div] using h

theorem coeff_eq_fourierCoeff_unitCircle {p : PowerSeries ℂ} {f : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars ℂ (fun k => PowerSeries.coeff (R := ℂ) k p)) 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 1)) (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n p =
      fourierCoeff (fun t : AddCircle (2 * Real.pi) => f (fourier 1 t)) (n : ℤ) := by
  rw [coeff_eq_unitCircle_cauchyIntegral hf hd n, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, circleIntegral, deriv_circleMap, smul_eq_mul, Complex.real_smul]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  simp only [circleMap_zero_one_eq_fourier, fourier_neg_natCast_eq_inv_pow]
  push_cast
  field_simp [Complex.I_ne_zero,
    show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero]

end DirichletL
