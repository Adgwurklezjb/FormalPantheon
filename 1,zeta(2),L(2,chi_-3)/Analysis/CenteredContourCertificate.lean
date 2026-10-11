import Analysis.CenteredContourComponentCertificate
import Analysis.CenteredContourEnclosure

/-!
Checked root data for the complete corrected CDT contour, author Appendix A.4 page 204.
Complete meanings and parameter order precede these bodies in
-/

namespace DirichletL.CenteredRectangle

/-- Root data in the corrected order of four slits followed by the lune. -/
structure ContourCertificate where
  /-- Root data for the first slit, after shrinking the input. -/
  slit1 : SlitCertificate
  /-- Root data for the second slit, after rotation by 7977/100000 turns. -/
  slit2 : SlitCertificate
  /-- Root data for the third slit, after rotation by 11543/100000 turns. -/
  slit3 : SlitCertificate
  /-- Root data for the fourth slit, after rotation by 3525/100000 turns. -/
  slit4 : SlitCertificate
  /-- Root data for the lune, after the final rotation and negation. -/
  lune : LuneCertificate

/-- Evaluate the entire corrected contour using checked roots of actual intermediate inputs. -/
def contourWithRoots? (D : ℕ) (B : CenteredRectangle) (cert : ContourCertificate) :
    Option CenteredRectangle := do
  let B1 ← slitWithRoots? D (91 / 100) (scale D (995 / 1000) B) cert.slit1
  let B2 ← slitWithRoots? D (6188 / 10000) (rotate D 7977 100000 B1) cert.slit2
  let B3 ← slitWithRoots? D (55515 / 100000) (rotate D 11543 100000 B2) cert.slit3
  let B4 ← slitWithRoots? D (772 / 1000) (rotate D 3525 100000 B3) cert.slit4
  let B5 ← luneWithRoots? D (75 / 10) (neg (rotate D (-783) 10000 B4)) cert.lune
  return scale D (-77 / 100) B5

theorem contourWithRoots?_eq {D : ℕ} {B C : CenteredRectangle}
    {cert : ContourCertificate} (h : contourWithRoots? D B cert = some C) :
    contour? D B = some C := by
  dsimp only [contourWithRoots?] at h
  rcases Option.bind_eq_some.mp h with ⟨B1, hB1, h⟩
  rcases Option.bind_eq_some.mp h with ⟨B2, hB2, h⟩
  rcases Option.bind_eq_some.mp h with ⟨B3, hB3, h⟩
  rcases Option.bind_eq_some.mp h with ⟨B4, hB4, h⟩
  rcases Option.bind_eq_some.mp h with ⟨B5, hB5, h⟩
  dsimp only [contour?]
  apply Option.bind_eq_some.mpr
  refine ⟨B1, slitWithRoots?_eq hB1, ?_⟩
  apply Option.bind_eq_some.mpr
  refine ⟨B2, slitWithRoots?_eq hB2, ?_⟩
  apply Option.bind_eq_some.mpr
  refine ⟨B3, slitWithRoots?_eq hB3, ?_⟩
  apply Option.bind_eq_some.mpr
  refine ⟨B4, slitWithRoots?_eq hB4, ?_⟩
  exact Option.bind_eq_some.mpr ⟨B5, luneWithRoots?_eq hB5, h⟩

theorem contourWithRoots?_encloses {D : ℕ} (hD : 0 < D)
    {B C : CenteredRectangle} {cert : ContourCertificate} {z z0 : ℂ}
    (hC : contourWithRoots? D B cert = some C) (h : Encloses D B z z0) :
    Encloses D C (cdtContourDiskMap z) (cdtContourDiskMap z0) :=
  contour?_encloses hD (contourWithRoots?_eq hC) h

end DirichletL.CenteredRectangle
