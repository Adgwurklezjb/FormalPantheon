import Arithmetic.IntegerDenominators

/-!
Integer-image products for the partially cleared coefficients in CDT v2,
supplied TeX 4440-4518. Degree zero uses the separately integral constant.
-/

namespace DirichletL

theorem isInteger_nat_mul_prod {ι : Type*} (s : Finset ι) (d : ι → ℕ) (f : ι → ℚ)
    (h : ∀ i ∈ s, IsLocalization.IsInteger ℤ ((d i : ℚ) * f i)) :
    IsLocalization.IsInteger ℤ (((∏ i ∈ s, d i : ℕ) : ℚ) * ∏ i ∈ s, f i) := by
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
  exact (algebraMap ℤ ℚ).rangeS.prod_mem h

theorem isInteger_max_one_pow_mul {n e : ℕ} {q : ℚ}
    (hzero : n = 0 → IsLocalization.IsInteger ℤ q)
    (h : IsLocalization.IsInteger ℤ ((n : ℚ) ^ e * q)) :
    IsLocalization.IsInteger ℤ ((((max 1 n) ^ e : ℕ) : ℚ) * q) := by
  by_cases hn : n = 0
  · subst n
    simpa using hzero rfl
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
    simpa only [max_eq_right hn1, Nat.cast_pow] using h

end DirichletL
