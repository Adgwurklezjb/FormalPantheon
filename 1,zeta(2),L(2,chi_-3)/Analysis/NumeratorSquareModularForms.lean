import Analysis.BetaNumeratorFourier
import Analysis.GammaNumeratorFourier
import Analysis.CharacterCubicModularForms

/-!
The literal CDT numerator squares as weight-six modular forms on Γ₀(6).
The normalization uses the full Fourier identities for the cubic lattice sums.
Source: CDT v2, Section 11.1; Zagier (2009), Section 6.
-/

namespace DirichletL

open CongruenceSubgroup
open _root_.UpperHalfPlane

/-- The square of the beta numerator series as a weight-six modular form. -/
noncomputable def betaNumeratorSquareForm : ModularForm (Gamma0 6) 6 :=
  betaCubicFourierConstant⁻¹ ^ 2 • betaCubicSquareForm

/-- The square of the gamma numerator series as a weight-six modular form. -/
noncomputable def gammaNumeratorSquareForm : ModularForm (Gamma0 6) 6 :=
  gammaCubicFourierConstant⁻¹ ^ 2 • gammaCubicSquareForm

theorem betaNumeratorSquareForm_apply (τ : ℍ) :
    betaNumeratorSquareForm τ =
      (∑' n : ℕ, (betaNumerator n : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ n) ^ 2 := by
  change betaCubicFourierConstant⁻¹ ^ 2 * betaCubicSquareForm τ = _
  rw [betaCubicSquareForm_apply, weightedCubicEisenstein_beta_eq_tsum]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  change betaCubicFourierConstant⁻¹ ^ 2 * (betaCubicFourierConstant * _) ^ 2 = _
  rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ betaCubicFourierConstant_ne_zero,
    one_pow, one_mul]

theorem gammaNumeratorSquareForm_apply (τ : ℍ) :
    gammaNumeratorSquareForm τ =
      (∑' n : ℕ, (gammaNumerator n : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ n) ^ 2 := by
  change gammaCubicFourierConstant⁻¹ ^ 2 * gammaCubicSquareForm τ = _
  rw [gammaCubicSquareForm_apply, weightedCubicEisenstein_gamma_eq_tsum]
  simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
  rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ gammaCubicFourierConstant_ne_zero,
    one_pow, one_mul]

end DirichletL
