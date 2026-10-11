import Analysis.CenteredLogProfile
import Analysis.CenteredContourEnclosure
import Analysis.CenteredCircleCell
import Analysis.ContourMap
import Analysis.CircleLogProfile

/-!
Closed-cell profiles for CDT's corrected contour, author pages 174 and 204.
Meanings, angle conventions, and endpoints precede these bodies in
-/

namespace DirichletL.CenteredRectangle

/-- Evaluate the corrected contour and complete logarithmic profile on a closed circle cell. -/
def circleLogProfile? (D : ℕ) (inner : Bool) (l u : ℚ) (kq kp : ℤ × ℤ) :
    Option (NonemptyInterval ℤ) := do
  let B ← contour? D (circleCell D inner l u)
  logProfile? D B kq kp

theorem circleLogProfile?_mem {D : ℕ} (hD : 0 < D) (inner : Bool)
    (l u : ℚ) (kq kp : ℤ × ℤ) {I : NonemptyInterval ℤ} {x : ℝ}
    (hI : circleLogProfile? D inner l u kq kp = some I)
    (hx : x ∈ Set.Icc (l : ℝ) (u : ℝ)) :
    let r : ℝ := if inner then Real.exp (-1 / 2) else 1
    circleLogProfile (fun z => cdtContourMap ((r : ℂ) * z)) x ∈
      ScaledInterval.denote D I := by
  let r : ℝ := if inner then Real.exp (-1 / 2) else 1
  have hr0 : 0 ≤ r := by
    cases inner <;> simp only [r, Bool.false_eq_true, ↓reduceIte] <;> positivity
  have hr1 : r ≤ 1 := by
    cases inner
    · norm_num [r]
    · simpa only [r, ↓reduceIte, Real.exp_zero] using
        (Real.exp_le_exp.mpr (by norm_num : (-1 / 2 : ℝ) ≤ 0))
  have hz (t : ℝ) : ‖(r : ℂ) * contourRotation t‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      norm_contourRotation, mul_one] using hr1
  rcases Option.bind_eq_some.mp hI with ⟨B, hB, hI⟩
  have hc := contour?_encloses hD hB (circleCell_encloses hD inner l u hx)
  have hq := norm_cdtContourDiskMap_lt (hz x)
  have hq₀ := norm_cdtContourDiskMap_lt (hz (((l : ℝ) + (u : ℝ)) / 2))
  simpa only [circleLogProfile, cdtContourMap, contourRotation_eq_fourier, r] using
    logProfile?_mem hD kq kp hI hc hq.le hq₀.le

end DirichletL.CenteredRectangle
