import Analysis.CenteredContourComponents

/-!
Interpret the exact corrected contour from CDT author Appendix A.4, page 204.
Meanings and parameter checks precede these bodies in
-/

namespace DirichletL.CenteredRectangle

/-- Checked midpoint and whole-cell evaluation of the corrected CDT disk map. -/
def contour? (D : ℕ) (B : CenteredRectangle) : Option CenteredRectangle := do
  let B1 ← slit? D (91 / 100) (scale D (995 / 1000) B)
  let B2 ← slit? D (6188 / 10000) (rotate D 7977 100000 B1)
  let B3 ← slit? D (55515 / 100000) (rotate D 11543 100000 B2)
  let B4 ← slit? D (772 / 1000) (rotate D 3525 100000 B3)
  let B5 ← lune? D (75 / 10) (neg (rotate D (-783) 10000 B4))
  return scale D (-77 / 100) B5

theorem contour?_encloses {D : ℕ} (hD : 0 < D)
    {B C : CenteredRectangle} {z z0 : ℂ}
    (hC : contour? D B = some C) (h : Encloses D B z z0) :
    Encloses D C (cdtContourDiskMap z) (cdtContourDiskMap z0) := by
  rcases Option.bind_eq_some.mp hC with ⟨B1, hB1, hC⟩
  rcases Option.bind_eq_some.mp hC with ⟨B2, hB2, hC⟩
  rcases Option.bind_eq_some.mp hC with ⟨B3, hB3, hC⟩
  rcases Option.bind_eq_some.mp hC with ⟨B4, hB4, hC⟩
  rcases Option.bind_eq_some.mp hC with ⟨B5, hB5, hC⟩
  cases Option.some.inj hC
  have h1 := slit?_encloses hD _ hB1 (scale_encloses hD (995 / 1000) h)
  have h2 := slit?_encloses hD _ hB2
    (rotate_encloses hD 7977 100000 (by norm_num) (by norm_num [abs_div]) h1)
  have h3 := slit?_encloses hD _ hB3
    (rotate_encloses hD 11543 100000 (by norm_num) (by norm_num [abs_div]) h2)
  have h4 := slit?_encloses hD _ hB4
    (rotate_encloses hD 3525 100000 (by norm_num) (by norm_num [abs_div]) h3)
  have h5 := lune?_encloses hD _ hB5
    (neg_encloses hD (rotate_encloses hD (-783) 10000 (by norm_num)
      (by norm_num [abs_div]) h4))
  simpa only [cdtContourDiskMap, Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg,
    Int.cast_ofNat, Int.cast_neg, neg_mul, neg_div] using scale_encloses hD (-77 / 100) h5

end DirichletL.CenteredRectangle
