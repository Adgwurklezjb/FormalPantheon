import Analysis.ScaledRectangleNorm

/-!
Rational scalar bounds for CDT's contour cells, author Appendix A.4, page 204.
All meanings and rounding edge cases precede these bodies in
-/

namespace DirichletL.ScaledInterval

instance instDecidableEqNonemptyIntervalInt : DecidableEq (NonemptyInterval ℤ) :=
  NonemptyInterval.toProd_injective.decidableEq

/-- Outward enclosure of a canonical rational number. -/
def ofRat (D : ℕ) (q : ℚ) : NonemptyInterval ℤ := rational D q.num q.den

theorem ofRat_mem {D : ℕ} (hD : 0 < D) (q : ℚ) :
    (q : ℝ) ∈ denote D (ofRat D q) := by
  simpa only [ofRat, Rat.cast_def, Int.cast_natCast] using
    rational_mem hD q.num q.den (by exact_mod_cast q.pos)

/-- Round a rational number upwards to the grid with denominator `D`. -/
def roundUp (D : ℕ) (q : ℚ) : ℚ := (⌈(D : ℚ) * q⌉ : ℚ) / D

theorem le_roundUp {D : ℕ} (hD : 0 < D) (q : ℚ) :
    (q : ℝ) ≤ (roundUp D q : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have h : (D : ℝ) * (q : ℝ) ≤ (⌈(D : ℚ) * q⌉ : ℝ) := by
    exact_mod_cast Int.le_ceil ((D : ℚ) * q)
  simpa only [roundUp, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
    (le_div_iff₀ hDr).mpr (by simpa only [mul_comm] using h)

end DirichletL.ScaledInterval

namespace DirichletL.ScaledRectangle

/-- A canonical rational number embedded as a complex rectangle. -/
def ofRat (D : ℕ) (q : ℚ) : ScaledRectangle := rational D q.num q.den

theorem ofRat_mem {D : ℕ} (hD : 0 < D) (q : ℚ) :
    (q : ℂ) ∈ denote D (ofRat D q) := by
  simpa only [ofRat, Rat.cast_def, Int.cast_natCast] using
    rational_mem hD q.num q.den (by exact_mod_cast q.pos)

/-- The rational lower endpoint of the existing norm enclosure. -/
def normLower (D : ℕ) (Z : ScaledRectangle) : ℚ := ((norm D Z).fst : ℚ) / D

/-- The rational upper endpoint of the existing norm enclosure. -/
def normUpper (D : ℕ) (Z : ScaledRectangle) : ℚ := ((norm D Z).snd : ℚ) / D

theorem normLower_le_norm {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) : (normLower D Z : ℝ) ≤ ‖z‖ := by
  simpa only [normLower, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
    (norm_mem hD hz).1

theorem norm_le_normUpper {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) : ‖z‖ ≤ (normUpper D Z : ℝ) := by
  simpa only [normUpper, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
    (norm_mem hD hz).2

end DirichletL.ScaledRectangle
