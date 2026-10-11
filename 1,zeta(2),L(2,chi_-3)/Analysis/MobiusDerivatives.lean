import Analysis.MobiusDescent

/-!
Formal derivatives of the coordinate in CDT v2, equation `y in x`.
All inverse identities concern the unit `1 - X`; the ramified derivative of
`y` is never inverted in the power-series ring.
-/

namespace DirichletL

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "w" => mobiusInvolutionQ
local notation "u" => (1 - mobiusInvolutionQ)

theorem X_sub_one_mul_mobiusInvolutionQ : (x - 1) * w = x := by
  have hu : (1 - x) * PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1) = 1 := by
    simpa [pow_one] using congrArg (PowerSeries.map (Int.castRingHom ℚ))
      (oneSubInv_rightInv (k := 1) (by norm_num))
  dsimp [mobiusInvolutionQ, mobiusInvolution]
  rw [map_neg, map_mul, PowerSeries.map_X]
  linear_combination x * hu

theorem one_sub_X_mul_one_sub_mobiusInvolutionQ : (1 - x) * u = 1 := by
  linear_combination X_sub_one_mul_mobiusInvolutionQ

theorem derivative_mobiusInvolutionQ : D w = -u ^ 2 := by
  have h := (PowerSeries.derivative ℚ).leibniz_of_mul_eq_one
    (show u * (1 - x) = 1 by
      rw [mul_comm, one_sub_X_mul_one_sub_mobiusInvolutionQ])
  simp only [map_sub, Derivation.map_one_eq_zero, PowerSeries.derivative_X,
    zero_sub, smul_eq_mul] at h
  linear_combination -h

theorem derivative_two_mobiusInvolutionQ : D (D w) = -2 * u ^ 3 := by
  rw [derivative_mobiusInvolutionQ]
  simp only [map_neg, Derivation.leibniz_pow, map_sub, Derivation.map_one_eq_zero,
    derivative_mobiusInvolutionQ, smul_eq_mul, nsmul_eq_mul]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
  ring

theorem derivative_three_mobiusInvolutionQ : D (D (D w)) = -6 * u ^ 4 := by
  have h2 : D (2 : PowerSeries ℚ) = 0 := (PowerSeries.derivative ℚ).map_natCast 2
  rw [derivative_two_mobiusInvolutionQ]
  simp only [Derivation.leibniz, map_neg, Derivation.map_natCast,
    Derivation.leibniz_pow, map_sub, Derivation.map_one_eq_zero,
    derivative_mobiusInvolutionQ, h2, smul_eq_mul, nsmul_eq_mul]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
  ring

theorem derivative_four_mobiusInvolutionQ : D (D (D (D w))) = -24 * u ^ 5 := by
  have h6 : D (6 : PowerSeries ℚ) = 0 := (PowerSeries.derivative ℚ).map_natCast 6
  rw [derivative_three_mobiusInvolutionQ]
  simp only [Derivation.leibniz, map_neg, Derivation.map_natCast,
    Derivation.leibniz_pow, map_sub, Derivation.map_one_eq_zero,
    derivative_mobiusInvolutionQ, h6, smul_eq_mul, nsmul_eq_mul]
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
  ring

theorem derivative_mobiusCoordinateQ : D mobiusCoordinateQ = 1 - u ^ 2 := by
  simp [mobiusCoordinateQ, derivative_mobiusInvolutionQ, sub_eq_add_neg]

theorem derivative_two_mobiusCoordinateQ : D (D mobiusCoordinateQ) = -2 * u ^ 3 := by
  simpa [mobiusCoordinateQ] using derivative_two_mobiusInvolutionQ

theorem derivative_three_mobiusCoordinateQ :
    D (D (D mobiusCoordinateQ)) = -6 * u ^ 4 := by
  simpa [mobiusCoordinateQ] using derivative_three_mobiusInvolutionQ

theorem derivative_four_mobiusCoordinateQ :
    D (D (D (D mobiusCoordinateQ))) = -24 * u ^ 5 := by
  simpa [mobiusCoordinateQ] using derivative_four_mobiusInvolutionQ

end DirichletL
