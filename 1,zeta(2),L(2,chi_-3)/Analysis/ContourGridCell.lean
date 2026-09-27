import Analysis.CenteredContourCertificate
import Analysis.CenteredLogProfileCertificate
import Analysis.CircleLogProfileEnclosure

/-!
Grid cells for CDT's two-radius bound, author pages 174 and 204; supplied TeX 8384–8404.
Meanings and endpoint checks precede these bodies in
-/

namespace DirichletL

/-- A signed profile upper bound paired with its integer angular grid interval. -/
structure ContourGridCell where
  /-- Left angular endpoint, before division by the grid denominator. -/
  left : ℤ
  /-- Right angular endpoint, before division by the grid denominator. -/
  right : ℤ
  /-- Signed profile upper bound, before division by the value scale. -/
  upper : ℤ

namespace ContourGridCell

/-- Every point of the closed grid cell satisfies its actual contour profile bound. -/
def Bounded (D K : ℕ) (inner : Bool) (cell : ContourGridCell) : Prop :=
  let r : ℝ := if inner then Real.exp (-1 / 2) else 1
  ∀ x ∈ Set.Icc ((cell.left : ℝ) / K) ((cell.right : ℝ) / K),
    circleLogProfile (fun z => cdtContourMap ((r : ℂ) * z)) x ≤ (cell.upper : ℝ) / D

theorem bounded_of_checks {D K : ℕ} (hD : 0 < D)
    {inner : Bool} {cell : ContourGridCell} {B : CenteredRectangle}
    {cert : CenteredRectangle.ContourCertificate}
    {nomeRoots slopeRoots : ℕ × ℕ} {factorRoots : List (ℕ × ℕ)}
    {kq kp : ℤ × ℤ} {I : NonemptyInterval ℤ}
    (hcontour : CenteredRectangle.contourWithRoots? D
      (CenteredRectangle.circleCell D inner ((cell.left : ℚ) / K) ((cell.right : ℚ) / K))
      cert = some B)
    (hprofile : CenteredRectangle.logProfileWithRoots? D B
      nomeRoots slopeRoots factorRoots kq kp = some I)
    (hupper : I.snd ≤ cell.upper) : Bounded D K inner cell := by
  intro x hx
  have he : CenteredRectangle.circleLogProfile? D inner
      ((cell.left : ℚ) / K) ((cell.right : ℚ) / K) kq kp = some I :=
    Option.bind_eq_some.mpr ⟨B, CenteredRectangle.contourWithRoots?_eq hcontour,
      CenteredRectangle.logProfileWithRoots?_eq hprofile⟩
  have hv := CenteredRectangle.circleLogProfile?_mem hD inner
    ((cell.left : ℚ) / K) ((cell.right : ℚ) / K) kq kp he
    (by simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using hx)
  exact hv.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast hupper)
    (Nat.cast_nonneg D))

end ContourGridCell
end DirichletL
