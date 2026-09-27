import Analysis.ScaledRationalBounds

/-!
Rounded power errors for CDT v2's finite profile, TeX 8384-8404.
Meanings and the zero-index check precede these bodies in
-/

namespace DirichletL.ScaledInterval

/-- Rounded upper bound for the displacement of the next power. -/
def powerDifferenceRadius (D : ℕ) (δ : ℚ) (n : ℕ)
    (P : NonemptyInterval ℤ) : ℚ :=
  ((mul D (mul D (ofRat D ((n + 1 : ℕ) : ℚ)) P) (ofRat D δ)).snd : ℚ) / D

theorem le_powerDifferenceRadius {D : ℕ} (hD : 0 < D) (δ : ℚ) (n : ℕ)
    {P : NonemptyInterval ℤ} {ρ : ℝ} (hP : ρ ^ n ∈ denote D P) :
    ((n + 1 : ℕ) : ℝ) * ρ ^ n * (δ : ℝ) ≤
      (powerDifferenceRadius D δ n P : ℝ) := by
  have h := mul_mem hD (mul_mem hD (ofRat_mem hD ((n + 1 : ℕ) : ℚ)) hP)
    (ofRat_mem hD δ)
  simpa only [powerDifferenceRadius, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using h.2

/-- Rounded upper bound for the quadratic remainder of the next power. -/
def powerRemainderRadius (D : ℕ) (δ : ℚ) (n : ℕ)
    (P : NonemptyInterval ℤ) : ℚ :=
  ((mul D (mul D (mul D (ofRat D (((n + 1 : ℕ) : ℚ) * n / 2)) P)
    (ofRat D δ)) (ofRat D δ)).snd : ℚ) / D

theorem le_powerRemainderRadius {D : ℕ} (hD : 0 < D) (δ : ℚ) (n : ℕ)
    {P : NonemptyInterval ℤ} {ρ : ℝ} (hP : ρ ^ (n - 1) ∈ denote D P) :
    (((n + 1 : ℕ) : ℝ) * (n : ℝ) / 2) * ρ ^ (n - 1) * (δ : ℝ) ^ 2 ≤
      (powerRemainderRadius D δ n P : ℝ) := by
  have h := mul_mem hD
    (mul_mem hD (mul_mem hD (ofRat_mem hD (((n + 1 : ℕ) : ℚ) * n / 2)) hP)
      (ofRat_mem hD δ)) (ofRat_mem hD δ)
  simpa only [powerRemainderRadius, Rat.cast_div, Rat.cast_mul, Rat.cast_intCast,
    Rat.cast_natCast, Rat.cast_ofNat, pow_two, mul_assoc] using h.2

end DirichletL.ScaledInterval
