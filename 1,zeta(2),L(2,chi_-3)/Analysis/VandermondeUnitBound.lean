import Comparator.Statement

/-!
The universal upper bound for the other Vandermonde blocks in CDT v2,
supplied TeX 4069-4092, and published UDC Sections 2.5.3 and 2.5.14.
The sufficient factorial bound and edge cases are independently checked
-/

namespace DirichletL

theorem norm_vandermonde_le_factorial {b : ℕ} (z : Fin b → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) :
    ‖(Matrix.vandermonde z).det‖ ≤ (Nat.factorial b : ℝ) := by
  have h := Matrix.det_le (A := Matrix.vandermonde z)
    (abv := NormedField.toAbsoluteValue ℂ) (x := (1 : ℝ)) (fun i j => by
      change ‖z i ^ (j : ℕ)‖ ≤ 1
      simp only [norm_pow, hz i, one_pow, le_refl])
  simpa only [NormedField.toAbsoluteValue, Fintype.card_fin, one_pow,
    nsmul_eq_mul, mul_one] using h

theorem norm_vandermonde_le_pow {b d : ℕ} (hbd : b ≤ d) (z : Fin b → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) :
    ‖(Matrix.vandermonde z).det‖ ≤ (d : ℝ) ^ b := by
  calc
    ‖(Matrix.vandermonde z).det‖ ≤ (Nat.factorial b : ℝ) :=
      norm_vandermonde_le_factorial z hz
    _ ≤ (b : ℝ) ^ b := by exact_mod_cast Nat.factorial_le_pow b
    _ ≤ (d : ℝ) ^ b := pow_le_pow_left₀ (Nat.cast_nonneg b) (by exact_mod_cast hbd) b

theorem norm_vandermonde_le_exp {b d : ℕ} (hd : 0 < d) (hbd : b ≤ d)
    (z : Fin b → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    ‖(Matrix.vandermonde z).det‖ ≤ Real.exp ((b : ℝ) * Real.log (d : ℝ)) := by
  simpa only [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hd : (0 : ℝ) < d)]
    using norm_vandermonde_le_pow hbd z hz

end DirichletL
