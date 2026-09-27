import Analysis.CenteredRectangleBasic
import Analysis.ScaledRectangleChecked
import Analysis.ContourRootVariation

/-!
Checked quadratic arguments and principal roots for CDT v2, supplied TeX 10003-10019.
Meanings and branch guards precede these bodies in
-/

namespace DirichletL.CenteredRectangle

/-- Enclose the quadratic argument `(1-d)+d*z^2` and its variation. -/
def affineSquare (D : ℕ) (d : ℚ) (B : CenteredRectangle) : CenteredRectangle :=
  ⟨ScaledRectangle.ofRat D (1 - d) + ScaledRectangle.realMul D (ScaledInterval.ofRat D d)
      (ScaledRectangle.mul D B.center B.center),
    ScaledInterval.roundUp D
      (|d| * B.radius * (2 * ScaledRectangle.normUpper D B.center + B.radius))⟩

theorem affineSquare_encloses {D : ℕ} (hD : 0 < D) (d : ℚ)
    {B : CenteredRectangle} {z z0 : ℂ} (h : Encloses D B z z0) :
    Encloses D (affineSquare D d B)
      ((1 - (d : ℂ)) + (d : ℂ) * z ^ 2)
      ((1 - (d : ℂ)) + (d : ℂ) * z0 ^ 2) := by
  constructor
  · simpa only [Rat.cast_sub, Rat.cast_one, Complex.ofReal_ratCast, pow_two] using
      ScaledRectangle.add_mem hD (ScaledRectangle.ofRat_mem hD (1 - d))
        (ScaledRectangle.realMul_mem hD (ScaledInterval.ofRat_mem hD d)
          (ScaledRectangle.mul_mem hD h.1 h.1))
  · have hδ0 : 0 ≤ (B.radius : ℝ) := (norm_nonneg _).trans h.2
    have hU := ScaledRectangle.norm_le_normUpper hD h.1
    calc
      _ = |(d : ℝ)| * ‖z ^ 2 - z0 ^ 2‖ := by
        rw [show ((1 - (d : ℂ)) + (d : ℂ) * z ^ 2) -
          ((1 - (d : ℂ)) + (d : ℂ) * z0 ^ 2) = (d : ℂ) * (z ^ 2 - z0 ^ 2) by ring]
        rw [norm_mul, Complex.norm_ratCast]
      _ ≤ |(d : ℝ)| * ((B.radius : ℝ) * (2 * ‖z0‖ + (B.radius : ℝ))) :=
        mul_le_mul_of_nonneg_left (norm_sq_sub_sq_le_of_norm_sub_le h.2) (abs_nonneg _)
      _ ≤ |(d : ℝ)| * (B.radius : ℝ) *
          (2 * (ScaledRectangle.normUpper D B.center : ℝ) + (B.radius : ℝ)) := by
        rw [mul_assoc]
        gcongr
      _ ≤ _ := by
        simpa only [Rat.cast_mul, Rat.cast_abs, Rat.cast_add, Rat.cast_ofNat] using
          ScaledInterval.le_roundUp hD
            (|d| * B.radius * (2 * ScaledRectangle.normUpper D B.center + B.radius))

/-- Enclose principal roots at the midpoint and on the inflated argument rectangle. -/
def sqrt? (D : ℕ) (B : CenteredRectangle) : Option CenteredRectangle := do
  let V ← ScaledRectangle.sqrt? D B.center
  let W ← ScaledRectangle.sqrt? D (ScaledRectangle.inflate ⌈(D : ℚ) * B.radius⌉ B.center)
  let β := ScaledRectangle.normLower D (W + V)
  if 0 < β then
    return ⟨V, ScaledInterval.roundUp D (B.radius / β)⟩
  else none

theorem sqrt?_encloses {D : ℕ} (hD : 0 < D)
    {B C : CenteredRectangle} {z z0 : ℂ}
    (hC : sqrt? D B = some C) (h : Encloses D B z z0) :
    Encloses D C (z ^ (2⁻¹ : ℂ)) (z0 ^ (2⁻¹ : ℂ)) := by
  dsimp only [sqrt?] at hC
  rcases Option.bind_eq_some.mp hC with ⟨V, hV, hC⟩
  rcases Option.bind_eq_some.mp hC with ⟨W, hW, hC⟩
  split at hC
  · rename_i hguard
    cases Option.some.inj hC
    have hm := ScaledRectangle.sqrt?_mem hD hV h.1
    have hz : z ∈ ScaledRectangle.denote D
        (ScaledRectangle.inflate ⌈(D : ℚ) * B.radius⌉ B.center) := by
      apply ScaledRectangle.inflate_mem hD h.1
      simpa only [ScaledInterval.roundUp, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
        using h.2.trans (ScaledInterval.le_roundUp hD B.radius)
    have hw := ScaledRectangle.sqrt?_mem hD hW hz
    have hβ := ScaledRectangle.normLower_le_norm hD (ScaledRectangle.add_mem hD hw hm)
    refine ⟨hm, ?_⟩
    apply (norm_cpow_inv_two_sub_le h.2 hβ (by exact_mod_cast hguard)).trans
    simpa only [Rat.cast_div] using
      ScaledInterval.le_roundUp hD (B.radius / ScaledRectangle.normLower D (W + V))
  · cases hC

end DirichletL.CenteredRectangle
