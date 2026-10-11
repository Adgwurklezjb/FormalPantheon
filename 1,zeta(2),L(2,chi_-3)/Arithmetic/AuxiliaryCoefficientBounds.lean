import Arithmetic.AuxiliaryCoefficientDenominators
import Analysis.AuxiliaryFormalSeriesScaling

/-!
The actual auxiliary coefficient denominator and its logarithmic lower bound,
from CDT v2 TeX 3965-3998, 4304-4404, and 4440-4518. Meanings and the fixed
multiplier's sign and exponent are checked before these proofs in
-/

namespace DirichletL

theorem exists_int_pow_cdtAuxiliary_coeff_denominators (a b c : ℤ) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ (h D : ℕ) (ε δ : ℝ)
      (t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ) (n : Fin (14 * h) →₀ ℕ)
      (σ : Equiv.Perm (Fin (14 * h))),
      (∀ j, (n (σ j) : ℝ) ≤ D * (δ + ((j : ℝ) + 1) / h)) →
      IsLocalization.IsInteger ℤ
        ((cdt14CoefficientDenominator h D ρ δ
          (Function.extend Fin.val (fun j => n (σ j)) (fun _ => 0)) : ℚ) *
          (M : ℚ) ^ (14 * h) *
          MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t)) := by
  obtain ⟨M, hM, hzero, hcoeff⟩ := exists_int_smul_cdtHolonomySeries_denominators a b c hρ
  refine ⟨M, hM, ?_⟩
  intro h D ε δ t n σ hn
  have hc := isInteger_cdt14CoefficientDenominator_mul_auxiliary_coeff
    (fun i => (M : ℚ) • cdtHolonomySeries a b c i) h D ε
    (by linarith : 0 ≤ 2 + ρ) hzero hcoeff t n σ hn
  simpa only [auxiliaryFormalSeries_smul_family, MvPowerSeries.coeff_smul,
    mul_assoc] using hc

theorem neg_log_abs_le_of_isInteger_nat_mul_int_pow (N : ℕ) (M : ℤ) (d : ℕ) (β : ℚ)
    (hN : 0 < N) (hM : M ≠ 0) (hβ : β ≠ 0)
    (hI : IsLocalization.IsInteger ℤ ((N : ℚ) * (M : ℚ) ^ d * β)) :
    -Real.log |(β : ℝ)| ≤ Real.log (N : ℝ) + (d : ℝ) * Real.log |(M : ℝ)| := by
  have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hMQ : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  have hprod : (N : ℚ) * (M : ℚ) ^ d * β ≠ 0 :=
    mul_ne_zero (mul_ne_zero hNQ (pow_ne_zero d hMQ)) hβ
  obtain ⟨z, hz⟩ := hI
  change (z : ℚ) = (N : ℚ) * (M : ℚ) ^ d * β at hz
  have hz0 : z ≠ 0 := by
    intro h
    apply hprod
    simpa only [h, Int.cast_zero] using hz.symm
  have hzR : (z : ℝ) = (N : ℝ) * (M : ℝ) ^ d * (β : ℝ) := by exact_mod_cast hz
  have hlow : (1 : ℝ) ≤ |(N : ℝ) * (M : ℝ) ^ d * (β : ℝ)| := by
    rw [← hzR]
    exact_mod_cast Int.one_le_abs hz0
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have hβR : (β : ℝ) ≠ 0 := by exact_mod_cast hβ
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hlow
  simp only [Real.log_one, abs_mul, abs_pow, abs_of_pos hNR] at hlog
  rw [Real.log_mul (mul_ne_zero hNR.ne' (pow_ne_zero d (abs_ne_zero.mpr hMR)))
      (abs_ne_zero.mpr hβR),
    Real.log_mul hNR.ne' (pow_ne_zero d (abs_ne_zero.mpr hMR)), Real.log_pow] at hlog
  linarith

end DirichletL
