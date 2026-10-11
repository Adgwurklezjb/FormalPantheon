import Foundations.ChiMinusThree

/-!
The exact third-root character transform and cubic Fourier normalizers
for CDT v2, Section 11.1. The source and polynomial checks are recorded
-/

namespace DirichletL

/-- The specified complex primitive third root for the gamma character transform. -/
noncomputable def cubicFourierRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem isPrimitiveRoot_cubicFourierRoot : IsPrimitiveRoot cubicFourierRoot 3 :=
  Complex.isPrimitiveRoot_exp 3 (by decide)

theorem cubicFourierRoot_sum : cubicFourierRoot ^ 2 + cubicFourierRoot + 1 = 0 := by
  have h := isPrimitiveRoot_cubicFourierRoot.geom_sum_eq_zero (by decide : 1 < 3)
  norm_num [Finset.sum_range_succ] at h
  linear_combination h

theorem cubicFourierRoot_character (n : ℕ) :
    cubicFourierRoot ^ n - cubicFourierRoot ^ (2 * n) =
      (cubicFourierRoot - cubicFourierRoot ^ 2) * (chiMinusThreeInt n : ℂ) := by
  have hm : chiMinusThreeInt n = chiMinusThreeInt (n % 3) := by
    simpa only [chiMinusThreeInt, Int.natCast_mod, Nat.cast_ofNat] using
      legendreSym.mod 3 (n : ℤ)
  rw [pow_eq_pow_mod n isPrimitiveRoot_cubicFourierRoot.pow_eq_one,
    pow_eq_pow_mod (2 * n) isPrimitiveRoot_cubicFourierRoot.pow_eq_one, hm, Nat.mul_mod]
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hn with h | h | h <;> rw [h] <;>
    norm_num [chiMinusThreeInt_zero, chiMinusThreeInt_one, chiMinusThreeInt_two]

theorem cubicFourierRoot_difference_sq :
    (cubicFourierRoot - cubicFourierRoot ^ 2) ^ 2 = -3 := by
  linear_combination (cubicFourierRoot ^ 2 - 3 * cubicFourierRoot + 3) * cubicFourierRoot_sum

theorem cubicFourierRoot_difference_ne_zero : cubicFourierRoot - cubicFourierRoot ^ 2 ≠ 0 := by
  intro h
  have hs := cubicFourierRoot_difference_sq
  rw [h] at hs
  norm_num at hs

/-- The exact nonzero scalar in the beta lattice Fourier expansion. -/
noncomputable def betaCubicFourierConstant : ℂ := 8 * (Real.pi : ℂ) ^ 3 * Complex.I

theorem betaCubicFourierConstant_ne_zero : betaCubicFourierConstant ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero))) Complex.I_ne_zero

theorem betaCubicFourierConstant_sq :
    betaCubicFourierConstant ^ 2 = -64 * (Real.pi : ℂ) ^ 6 := by
  simp only [betaCubicFourierConstant, mul_pow, ← pow_mul, Complex.I_sq]
  ring

/-- The exact scalar from the gamma character transform and modulus-three denominator. -/
noncomputable def gammaCubicFourierConstant : ℂ :=
  betaCubicFourierConstant * (cubicFourierRoot - cubicFourierRoot ^ 2) / 27

theorem gammaCubicFourierConstant_ne_zero : gammaCubicFourierConstant ≠ 0 :=
  div_ne_zero (mul_ne_zero betaCubicFourierConstant_ne_zero
    cubicFourierRoot_difference_ne_zero) (by norm_num)

theorem gammaCubicFourierConstant_sq :
    gammaCubicFourierConstant ^ 2 = (64 / 243 : ℂ) * (Real.pi : ℂ) ^ 6 := by
  rw [gammaCubicFourierConstant, div_pow, mul_pow,
    betaCubicFourierConstant_sq, cubicFourierRoot_difference_sq]
  ring

end DirichletL
