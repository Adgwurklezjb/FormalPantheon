import Arithmetic.Denominators

/-!
Integer-image clearing operations for CDT v2, Lemma `bdenominators`
(supplied TeX 7443-7465). These retain the single lcm factors needed
by B2 and B3 and relate them to the existing squared clearing predicate.
-/

namespace DirichletL

theorem isInteger_nat_mul_of_dvd {q : ℚ} {m n : ℕ}
    (hq : IsLocalization.IsInteger ℤ ((m : ℚ) * q)) (hmn : m ∣ n) :
    IsLocalization.IsInteger ℤ ((n : ℚ) * q) := by
  obtain ⟨k, rfl⟩ := hmn
  obtain ⟨z, hz⟩ := hq
  change (z : ℚ) = (m : ℚ) * q at hz
  refine ⟨(k : ℤ) * z, ?_⟩
  change (((k : ℤ) * z : ℤ) : ℚ) = ((m * k : ℕ) : ℚ) * q
  rw [Int.cast_mul, Int.cast_natCast, hz, Nat.cast_mul]
  ring

theorem isInteger_nat_mul_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (m : ℕ)
    (h : ∀ i ∈ s, IsLocalization.IsInteger ℤ ((m : ℚ) * f i)) :
    IsLocalization.IsInteger ℤ ((m : ℚ) * ∑ i ∈ s, f i) := by
  rw [Finset.mul_sum]
  exact (algebraMap ℤ ℚ).rangeS.sum_mem h

theorem isInteger_nat_mul_mul_int {q : ℚ} {m : ℕ}
    (hq : IsLocalization.IsInteger ℤ ((m : ℚ) * q)) (z : ℤ) :
    IsLocalization.IsInteger ℤ ((m : ℚ) * (q * z)) := by
  rw [← mul_assoc]
  exact IsLocalization.isInteger_mul hq ⟨z, rfl⟩

theorem isInteger_nat_mul_sub {q r : ℚ} {m : ℕ}
    (hq : IsLocalization.IsInteger ℤ ((m : ℚ) * q))
    (hr : IsLocalization.IsInteger ℤ ((m : ℚ) * r)) :
    IsLocalization.IsInteger ℤ ((m : ℚ) * (q - r)) := by
  obtain ⟨z, hz⟩ := hq
  obtain ⟨w, hw⟩ := hr
  change (z : ℚ) = (m : ℚ) * q at hz
  change (w : ℚ) = (m : ℚ) * r at hw
  refine ⟨z - w, ?_⟩
  change ((z - w : ℤ) : ℚ) = _
  rw [Int.cast_sub, hz, hw, mul_sub]

theorem sqIntegral_iff_isInteger (q : ℚ) (m : ℕ) :
    SqIntegral q m ↔ IsLocalization.IsInteger ℤ ((m : ℚ) ^ 2 * q) := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

theorem isInteger_nat_mul_div {q : ℚ} {m n : ℕ} (hn : n ≠ 0)
    (hq : IsLocalization.IsInteger ℤ ((m : ℚ) * q)) :
    IsLocalization.IsInteger ℤ (((n * m : ℕ) : ℚ) * (q / n)) := by
  convert hq using 1
  push_cast
  field_simp

end DirichletL
