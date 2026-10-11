import Analysis.ScaledIntervalDivision

/-!
Complex enclosures for CDT's corrected contour (author revision, A.4, page 204).
-/

namespace DirichletL

/-- Integer intervals for the real and imaginary coordinates at a common scale. -/
abbrev ScaledRectangle := NonemptyInterval ℤ × NonemptyInterval ℤ

namespace ScaledRectangle

/-- The complex rectangle represented by a pair of scaled integer intervals. -/
def denote (D : ℕ) (Z : ScaledRectangle) : Set ℂ :=
  {z | z.re ∈ ScaledInterval.denote D Z.1 ∧ z.im ∈ ScaledInterval.denote D Z.2}

/-- Embed a real interval with an exact zero imaginary coordinate. -/
def ofReal (I : NonemptyInterval ℤ) : ScaledRectangle := (I, 0)

theorem ofReal_mem {D : ℕ} (hD : 0 < D) {I : NonemptyInterval ℤ} {a : ℝ}
    (ha : a ∈ ScaledInterval.denote D I) : (a : ℂ) ∈ denote D (ofReal I) := by
  refine ⟨ha, ?_⟩
  rw [ScaledInterval.mem_denote_iff hD]
  simp [ofReal]

/-- A rational real constant as a complex rectangle. -/
def rational (D : ℕ) (n d : ℤ) : ScaledRectangle := ofReal (ScaledInterval.rational D n d)

theorem rational_mem {D : ℕ} (hD : 0 < D) (n d : ℤ) (hd : 0 < d) :
    (n : ℂ) / (d : ℂ) ∈ denote D (rational D n d) := by
  simpa only [Complex.ofReal_div, Complex.ofReal_intCast] using
    ofReal_mem hD (ScaledInterval.rational_mem hD n d hd)

theorem add_mem {D : ℕ} (hD : 0 < D) {Z W : ScaledRectangle} {z w : ℂ}
    (hz : z ∈ denote D Z) (hw : w ∈ denote D W) : z + w ∈ denote D (Z + W) :=
  ⟨ScaledInterval.add_mem hD hz.1 hw.1, ScaledInterval.add_mem hD hz.2 hw.2⟩

theorem neg_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) : -z ∈ denote D (-Z) :=
  ⟨ScaledInterval.neg_mem hD hz.1, ScaledInterval.neg_mem hD hz.2⟩

theorem sub_mem {D : ℕ} (hD : 0 < D) {Z W : ScaledRectangle} {z w : ℂ}
    (hz : z ∈ denote D Z) (hw : w ∈ denote D W) : z - w ∈ denote D (Z - W) :=
  ⟨ScaledInterval.sub_mem hD hz.1 hw.1, ScaledInterval.sub_mem hD hz.2 hw.2⟩

/-- Multiply both coordinates by a real scaled interval. -/
def realMul (D : ℕ) (I : NonemptyInterval ℤ) (Z : ScaledRectangle) : ScaledRectangle :=
  (ScaledInterval.mul D I Z.1, ScaledInterval.mul D I Z.2)

theorem realMul_mem {D : ℕ} (hD : 0 < D) {I : NonemptyInterval ℤ}
    {Z : ScaledRectangle} {a : ℝ} {z : ℂ}
    (ha : a ∈ ScaledInterval.denote D I) (hz : z ∈ denote D Z) :
    (a : ℂ) * z ∈ denote D (realMul D I Z) := by
  constructor
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using ScaledInterval.mul_mem hD ha hz.1
  · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      using ScaledInterval.mul_mem hD ha hz.2

/-- Complex multiplication using four signed real interval products. -/
def mul (D : ℕ) (Z W : ScaledRectangle) : ScaledRectangle :=
  (ScaledInterval.mul D Z.1 W.1 - ScaledInterval.mul D Z.2 W.2,
    ScaledInterval.mul D Z.1 W.2 + ScaledInterval.mul D Z.2 W.1)

theorem mul_mem {D : ℕ} (hD : 0 < D) {Z W : ScaledRectangle} {z w : ℂ}
    (hz : z ∈ denote D Z) (hw : w ∈ denote D W) :
    z * w ∈ denote D (mul D Z W) :=
  ⟨ScaledInterval.sub_mem hD (ScaledInterval.mul_mem hD hz.1 hw.1)
      (ScaledInterval.mul_mem hD hz.2 hw.2),
    ScaledInterval.add_mem hD (ScaledInterval.mul_mem hD hz.1 hw.2)
      (ScaledInterval.mul_mem hD hz.2 hw.1)⟩

end ScaledRectangle
end DirichletL
