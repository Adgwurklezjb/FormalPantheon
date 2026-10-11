import Analysis.ScaledRectangleBasic

/-!
Norms and division for CDT's corrected contour (author revision, A.4, page 204).
-/

namespace DirichletL.ScaledRectangle

/-- Conjugate by negating the imaginary interval. -/
def conj (Z : ScaledRectangle) : ScaledRectangle := (Z.1, -Z.2)

theorem conj_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) : (starRingEnd ℂ) z ∈ denote D (conj Z) :=
  ⟨hz.1, ScaledInterval.neg_mem hD hz.2⟩

/-- A nonnegative enclosure of the sum of the squared coordinates. -/
def normSq (D : ℕ) (Z : ScaledRectangle) : NonemptyInterval ℤ :=
  ScaledInterval.square D Z.1 + ScaledInterval.square D Z.2

theorem normSq_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) : Complex.normSq z ∈ ScaledInterval.denote D (normSq D Z) := by
  simpa only [Complex.normSq_apply, pow_two] using
    ScaledInterval.add_mem hD (ScaledInterval.square_mem hD hz.1)
      (ScaledInterval.square_mem hD hz.2)

/-- Take the real square root of the squared-norm interval. -/
def norm (D : ℕ) (Z : ScaledRectangle) : NonemptyInterval ℤ :=
  ScaledInterval.sqrt D (normSq D Z)

theorem norm_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hz : z ∈ denote D Z) : ‖z‖ ∈ ScaledInterval.denote D (norm D Z) :=
  ScaledInterval.sqrt_mem hD (Complex.normSq_nonneg z) (normSq_mem hD hz)

/-- Reciprocal using conjugation and the positive squared-norm enclosure. -/
def inv (D : ℕ) (Z : ScaledRectangle) : ScaledRectangle :=
  realMul D (ScaledInterval.inv D (normSq D Z)) (conj Z)

theorem inv_mem {D : ℕ} (hD : 0 < D) {Z : ScaledRectangle} {z : ℂ}
    (hZ : 0 < (normSq D Z).fst) (hz : z ∈ denote D Z) :
    z⁻¹ ∈ denote D (inv D Z) := by
  simpa only [Complex.inv_def, mul_comm] using
    realMul_mem hD (ScaledInterval.inv_mem hD hZ (normSq_mem hD hz)) (conj_mem hD hz)

/-- Divide through the squared-norm reciprocal enclosure. -/
def div (D : ℕ) (Z W : ScaledRectangle) : ScaledRectangle := mul D Z (inv D W)

theorem div_mem {D : ℕ} (hD : 0 < D) {Z W : ScaledRectangle} {z w : ℂ}
    (hW : 0 < (normSq D W).fst) (hz : z ∈ denote D Z) (hw : w ∈ denote D W) :
    z / w ∈ denote D (div D Z W) := by
  simpa only [div_eq_mul_inv] using mul_mem hD hz (inv_mem hD hW hw)

end DirichletL.ScaledRectangle
