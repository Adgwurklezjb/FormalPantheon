import Analysis.ScaledRationalBounds
import Analysis.ContourInputEnclosures

/-!
Midpoint rectangles and whole-cell radii for CDT's corrected contour, A.4, page 204.
-/

namespace DirichletL

/-- An enclosure of an exact center, together with a rational variation radius. -/
structure CenteredRectangle where
  /-- A rectangle containing the exact reference value. -/
  center : ScaledRectangle
  /-- An upper bound for the norm of the variation from the reference value. -/
  radius : ℚ
  deriving DecidableEq

namespace CenteredRectangle

/-- The exact midpoint is enclosed, and the actual value is within the stored radius. -/
def Encloses (D : ℕ) (B : CenteredRectangle) (z z0 : ℂ) : Prop :=
  z0 ∈ ScaledRectangle.denote D B.center ∧ ‖z - z0‖ ≤ (B.radius : ℝ)

/-- Multiply by a rational scalar, rounding the variation radius upwards. -/
def scale (D : ℕ) (a : ℚ) (B : CenteredRectangle) : CenteredRectangle :=
  ⟨ScaledRectangle.realMul D (ScaledInterval.ofRat D a) B.center,
    ScaledInterval.roundUp D (|a| * B.radius)⟩

theorem scale_encloses {D : ℕ} (hD : 0 < D) (a : ℚ)
    {B : CenteredRectangle} {z z0 : ℂ} (h : Encloses D B z z0) :
    Encloses D (scale D a B) ((a : ℂ) * z) ((a : ℂ) * z0) := by
  constructor
  · simpa only [Complex.ofReal_ratCast] using
      ScaledRectangle.realMul_mem hD (ScaledInterval.ofRat_mem hD a) h.1
  · calc
      _ = |(a : ℝ)| * ‖z - z0‖ := by rw [← mul_sub, norm_mul, Complex.norm_ratCast]
      _ ≤ |(a : ℝ)| * (B.radius : ℝ) :=
        mul_le_mul_of_nonneg_left h.2 (abs_nonneg _)
      _ ≤ _ := by simpa only [Rat.cast_mul, Rat.cast_abs] using
          ScaledInterval.le_roundUp hD (|a| * B.radius)

/-- Negate the exact center and every actual value without changing the radius. -/
def neg (B : CenteredRectangle) : CenteredRectangle := ⟨-B.center, B.radius⟩

theorem neg_encloses {D : ℕ} (hD : 0 < D)
    {B : CenteredRectangle} {z z0 : ℂ} (h : Encloses D B z z0) :
    Encloses D (neg B) (-z) (-z0) := by
  refine ⟨ScaledRectangle.neg_mem hD h.1, ?_⟩
  simpa only [neg_sub_neg, norm_sub_rev] using h.2

/-- Apply a proved rational phase enclosure; the unit phase preserves the radius. -/
def rotate (D : ℕ) (n d : ℤ) (B : CenteredRectangle) : CenteredRectangle :=
  ⟨ScaledRectangle.mul D (ScaledRectangle.rotation D n d) B.center, B.radius⟩

theorem rotate_encloses {D : ℕ} (hD : 0 < D) (n d : ℤ) (hd : 0 < d)
    (ht : |(n : ℝ) / (d : ℝ)| ≤ 1 / 2)
    {B : CenteredRectangle} {z z0 : ℂ} (h : Encloses D B z z0) :
    Encloses D (rotate D n d B)
      (contourRotation ((n : ℝ) / (d : ℝ)) * z)
      (contourRotation ((n : ℝ) / (d : ℝ)) * z0) := by
  refine ⟨ScaledRectangle.mul_mem hD (ScaledRectangle.rotation_mem hD n d hd ht) h.1, ?_⟩
  simpa only [← mul_sub, norm_mul, norm_contourRotation, one_mul] using h.2

end CenteredRectangle
end DirichletL
