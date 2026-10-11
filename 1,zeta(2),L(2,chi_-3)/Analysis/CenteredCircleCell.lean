import Analysis.CenteredRectangleBasic
import Analysis.CircleArcVariation

/-!
Whole circle-cell inputs for CDT's two-radius integral, author pages 174 and 204.
Meanings, periodic reduction, and endpoints precede these bodies in
-/

namespace DirichletL.ScaledRectangle

/-- Reduce arbitrary rational turns by an integer before evaluating their phase. -/
def rotationRat (D : ℕ) (q : ℚ) : ScaledRectangle :=
  let t := q - (⌊q + 1 / 2⌋ : ℚ)
  rotation D t.num t.den

theorem rotationRat_mem {D : ℕ} (hD : 0 < D) (q : ℚ) :
    contourRotation (q : ℝ) ∈ denote D (rotationRat D q) := by
  let k : ℤ := ⌊q + 1 / 2⌋
  let t : ℚ := q - (k : ℚ)
  have ht : |t| ≤ (1 / 2 : ℚ) := by
    have hl := Int.floor_le (q + 1 / 2)
    have hu := Int.lt_floor_add_one (q + 1 / 2)
    dsimp only [t, k]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have heq : contourRotation (q : ℝ) = contourRotation (t : ℝ) := by
    have hq : (q : ℝ) = (t : ℝ) + (k : ℝ) := by
      simp only [t, Rat.cast_sub, Rat.cast_intCast, sub_add_cancel]
    rw [hq, contourRotation_add_int]
  rw [heq]
  have htr : |(t : ℝ)| ≤ 1 / 2 := by
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr ht
  simpa only [Rat.cast_def, Int.cast_natCast] using
    rotation_mem hD t.num t.den (by exact_mod_cast t.pos)
      (by simpa only [Rat.cast_def] using htr)

end DirichletL.ScaledRectangle

namespace DirichletL.CenteredRectangle

/-- Enclose a closed angular cell at the inner or outer radius and its exact midpoint. -/
def circleCell (D : ℕ) (inner : Bool) (l u : ℚ) : CenteredRectangle :=
  let R := if inner then ScaledRectangle.innerRadius D else ScaledInterval.ofRat D 1
  let E := ScaledInterval.mul D
    (ScaledInterval.mul D (ScaledRectangle.piInterval D) (ScaledInterval.ofRat D (u - l))) R
  ⟨ScaledRectangle.realMul D R (ScaledRectangle.rotationRat D ((l + u) / 2)),
    (E.snd : ℚ) / D⟩

theorem circleCell_encloses {D : ℕ} (hD : 0 < D) (inner : Bool) (l u : ℚ)
    {x : ℝ} (hx : x ∈ Set.Icc (l : ℝ) (u : ℝ)) :
    let r : ℝ := if inner then Real.exp (-1 / 2) else 1
    Encloses D (circleCell D inner l u)
      ((r : ℂ) * contourRotation x)
      ((r : ℂ) * contourRotation (((l : ℝ) + (u : ℝ)) / 2)) := by
  let r : ℝ := if inner then Real.exp (-1 / 2) else 1
  let R := if inner then ScaledRectangle.innerRadius D else ScaledInterval.ofRat D 1
  have hr : r ∈ ScaledInterval.denote D R := by
    cases inner
    · simpa only [r, R, Bool.false_eq_true, ↓reduceIte, Rat.cast_one] using
        ScaledInterval.ofRat_mem hD 1
    · exact ScaledRectangle.innerRadius_mem hD
  have hr0 : 0 ≤ r := by
    cases inner <;> simp only [r, Bool.false_eq_true, ↓reduceIte] <;> positivity
  have ht := ScaledRectangle.rotationRat_mem hD ((l + u) / 2)
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] at ht
  refine ⟨ScaledRectangle.realMul_mem hD hr ht, ?_⟩
  have hw := ScaledInterval.ofRat_mem hD (u - l)
  simp only [Rat.cast_sub] at hw
  have hE := ScaledInterval.mul_mem hD
    (ScaledInterval.mul_mem hD (ScaledRectangle.pi_mem hD) hw) hr
  have hbound := norm_radius_contourRotation_sub_midpoint_le (r := r) hx
  rw [abs_of_nonneg hr0] at hbound
  apply hbound.trans
  simpa only [circleCell, R, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast,
    mul_comm, mul_left_comm, mul_assoc] using hE.2

end DirichletL.CenteredRectangle
