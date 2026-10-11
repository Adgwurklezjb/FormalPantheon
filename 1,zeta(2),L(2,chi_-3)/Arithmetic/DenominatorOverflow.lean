import Arithmetic.IntegerDenominators

/-!
Fixed denominator offsets and finite initial rescaling, for CDT v2,
Remark `rem:overflow` (supplied TeX 3549-3564). The integer multiplier
is nonzero and clears the constant coefficients explicitly.
-/

namespace DirichletL

open Filter

theorem eventually_nat_add_le_floor_mul (b c : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, b * n + c ≤ ⌊((b : ℝ) + ε) * (n : ℝ)⌋₊ := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((c : ℝ) / ε)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply Nat.le_floor
  have hcn : (c : ℝ) < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (hN.trans_le (by exact_mod_cast hn))
  push_cast
  nlinarith

theorem exists_int_mul_isInteger_of_eventually {ι : Type*} [Finite ι]
    (q : ι → ℕ → ℚ) (D : ι → ℕ → ℕ)
    (hq : ∀ᶠ n : ℕ in atTop, ∀ i, IsLocalization.IsInteger ℤ ((D i n : ℚ) * q i n)) :
    ∃ M : ℤ, M ≠ 0 ∧
      (∀ i, IsLocalization.IsInteger ℤ ((M : ℚ) * q i 0)) ∧
      ∀ i n, IsLocalization.IsInteger ℤ ((D i n : ℚ) * ((M : ℚ) * q i n)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hq
  obtain ⟨M, hM⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun j : ι × Fin (N + 1) => q j.1 j.2)
  have hsmall (i : ι) (n : ℕ) (hn : n ≤ N) :
      IsLocalization.IsInteger ℤ (((M : ℤ) : ℚ) * q i n) := by
    simpa [Algebra.smul_def] using hM (i, ⟨n, Nat.lt_succ_of_le hn⟩)
  refine ⟨(M : ℤ), mem_nonZeroDivisors_iff_ne_zero.mp M.property,
    (fun i => hsmall i 0 (Nat.zero_le N)), ?_⟩
  intro i n
  by_cases hn : n ≤ N
  · exact IsLocalization.isInteger_mul ⟨(D i n : ℤ), by simp⟩ (hsmall i n hn)
  · have hlate := IsLocalization.isInteger_mul
      (show IsLocalization.IsInteger ℤ (((M : ℤ) : ℚ)) from ⟨(M : ℤ), rfl⟩)
      (hN n (by omega) i)
    simpa only [mul_left_comm] using hlate

end DirichletL
