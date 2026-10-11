import Analysis.ReciprocalCubeFourier
import Analysis.CubicCharacterFourier

/-!
The character-twisted reciprocal-cube expansion used for the gamma
numerator of CDT v2, Section 11.1. See the residue and convergence ledger
-/

namespace DirichletL

private theorem norm_legendreSym_three_complex_le_one (d : ℤ) :
    ‖(legendreSym 3 d : ℂ)‖ ≤ 1 := by
  by_cases h : (d : ZMod 3) = 0
  · rw [(legendreSym.eq_zero_iff 3 d).mpr h]
    norm_num
  · rcases legendreSym.eq_one_or_neg_one 3 h with h | h <;> rw [h] <;> norm_num

theorem summable_twistedCubicRow {z : ℂ} (hz : 0 < z.im) :
    Summable (fun d : ℤ => (legendreSym 3 d : ℂ) / (3 * z + d) ^ 3) := by
  have h3 : 0 < (3 * z).im := by simpa using mul_pos (by norm_num : (0 : ℝ) < 3) hz
  apply Summable.of_norm_bounded (g := fun d : ℤ => ‖1 / (3 * z + d) ^ 3‖)
    (summable_norm_one_div_int_add_cube h3)
  intro d
  simp only [norm_div, norm_one]
  exact div_le_div_of_nonneg_right (norm_legendreSym_three_complex_le_one d) (norm_nonneg _)

private theorem twistedCubicRow_residue (z : ℂ) (a : Fin 3) :
    (∑' k : ℤ, (legendreSym 3 (k * 3 + a) : ℂ) / (3 * z + (k * 3 + a : ℤ)) ^ 3) =
      (chiMinusThreeInt a : ℂ) / 27 *
        ∑' k : ℤ, 1 / (z + (a : ℂ) / 3 + k) ^ 3 := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  have hc : legendreSym 3 (k * 3 + a) = chiMinusThreeInt a := by
    simp only [legendreSym, chiMinusThreeInt, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      show (3 : ZMod 3) = 0 by decide, mul_zero, zero_add]
  have hd : 3 * z + (k * 3 + a : ℤ) = 3 * (z + (a : ℂ) / 3 + k) := by
    push_cast
    ring
  rw [hc, hd, mul_pow, div_mul_eq_div_div]
  norm_num [div_eq_mul_inv]

private theorem cubicFourier_exp_shift (z : ℂ) (a : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (z + (a : ℂ) / 3)) =
      Complex.exp (2 * Real.pi * Complex.I * z) * cubicFourierRoot ^ a := by
  rw [mul_add, Complex.exp_add, cubicFourierRoot, ← Complex.exp_nat_mul]
  congr 2
  ring

theorem tsum_twistedCubicRow_fourier {z : ℂ} (hz : 0 < z.im) :
    (∑' d : ℤ, (legendreSym 3 d : ℂ) / (3 * z + d) ^ 3) =
      (gammaCubicFourierConstant / 2) *
        ∑' r : ℕ, (chiMinusThreeInt r : ℂ) * (r : ℂ) ^ 2 *
          Complex.exp (2 * Real.pi * Complex.I * z) ^ r := by
  let f : ℤ → ℂ := fun d => (legendreSym 3 d : ℂ) / (3 * z + d) ^ 3
  let e : Fin 3 × ℤ ≃ ℤ := (Equiv.prodComm (Fin 3) ℤ).trans (Int.divModEquiv 3).symm
  have hs : Summable (fun p : Fin 3 × ℤ => f (e p)) :=
    (e.summable_iff (f := f)).mpr (summable_twistedCubicRow hz)
  have hsplit : (∑' d : ℤ, f d) =
      1 / 27 * ((∑' k : ℤ, 1 / (z + (1 : ℂ) / 3 + k) ^ 3) -
        ∑' k : ℤ, 1 / (z + (2 : ℂ) / 3 + k) ^ 3) := by
    rw [← e.tsum_eq f, hs.tsum_prod]
    change (∑' a : Fin 3, ∑' k : ℤ,
      (legendreSym 3 (k * 3 + a) : ℂ) / (3 * z + (k * 3 + a : ℤ)) ^ 3) = _
    simp_rw [twistedCubicRow_residue]
    simp only [tsum_fintype, Fin.sum_univ_succ]
    norm_num [chiMinusThreeInt_zero, chiMinusThreeInt_one, chiMinusThreeInt_two]
    ring
  have h₁ : 0 < (z + (1 : ℂ) / 3).im := by simpa using hz
  have h₂ : 0 < (z + (2 : ℂ) / 3).im := by simpa using hz
  have hs₁ := summable_pow_mul_geometric_of_norm_lt_one 2
    (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z + (1 : ℂ) / 3, h₁⟩)
  have hs₂ := summable_pow_mul_geometric_of_norm_lt_one 2
    (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z + (2 : ℂ) / 3, h₂⟩)
  change Summable (fun r : ℕ => (r : ℂ) ^ 2 *
    Complex.exp (2 * Real.pi * Complex.I * (z + (1 : ℂ) / 3)) ^ r) at hs₁
  change Summable (fun r : ℕ => (r : ℂ) ^ 2 *
    Complex.exp (2 * Real.pi * Complex.I * (z + (2 : ℂ) / 3)) ^ r) at hs₂
  change (∑' d : ℤ, f d) = _
  rw [hsplit, tsum_one_div_int_add_cube h₁, tsum_one_div_int_add_cube h₂,
    ← mul_sub, ← hs₁.tsum_sub hs₂]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro r
  have he₁ := cubicFourier_exp_shift z 1
  have he₂ := cubicFourier_exp_shift z 2
  simp only [Nat.cast_one, Nat.cast_ofNat] at he₁ he₂
  rw [he₁, he₂]
  simp only [pow_one, mul_pow, ← pow_mul]
  have h := cubicFourierRoot_character r
  dsimp [gammaCubicFourierConstant, betaCubicFourierConstant]
  linear_combination (4 * (Real.pi : ℂ) ^ 3 * Complex.I / 27 *
    (r : ℂ) ^ 2 * Complex.exp (2 * Real.pi * Complex.I * z) ^ r) * h

end DirichletL
