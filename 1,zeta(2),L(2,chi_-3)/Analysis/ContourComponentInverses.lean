import Analysis.ContourHalfPlaneRoot

/-!
Inverse identities for CDT v2's slit expression, Appendix `Slits`, TeX 10003-10019.
-/

namespace DirichletL

theorem inverseCayleyMap_cayleyMap {z : ℂ} (hz : z ≠ 1) :
    inverseCayleyMap (cayleyMap z) = z := by
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have hadd : cayleyMap z + 1 = 2 / (1 - z) := by
    dsimp only [cayleyMap]
    field_simp
    ring
  have houter : cayleyMap z + 1 ≠ 0 := by
    rw [hadd]
    exact div_ne_zero (by norm_num) hden
  apply (div_eq_iff houter).mpr
  dsimp only [cayleyMap]
  field_simp
  ring

theorem cayleyMap_inverseCayleyMap {w : ℂ} (hw : w + 1 ≠ 0) :
    cayleyMap (inverseCayleyMap w) = w := by
  have hsub : 1 - inverseCayleyMap w = 2 / (w + 1) := by
    dsimp only [inverseCayleyMap]
    field_simp
    ring
  have houter : 1 - inverseCayleyMap w ≠ 0 := by
    rw [hsub]
    exact div_ne_zero (by norm_num) hw
  apply (div_eq_iff houter).mpr
  dsimp only [inverseCayleyMap]
  field_simp
  ring

theorem contourHalfPlaneRoot_inv {d : ℝ} (hd : d ≠ 0) {w : ℂ} (hw : 0 < w.re) :
    contourHalfPlaneRoot d⁻¹ (contourHalfPlaneRoot d w) = w := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have heq : (1 - ((d⁻¹ : ℝ) : ℂ)) + ((d⁻¹ : ℝ) : ℂ) *
      contourHalfPlaneRoot d w ^ 2 = w ^ 2 := by
    rw [sq_contourHalfPlaneRoot, Complex.ofReal_inv]
    field_simp
    ring
  change ((1 - ((d⁻¹ : ℝ) : ℂ)) + ((d⁻¹ : ℝ) : ℂ) *
    contourHalfPlaneRoot d w ^ 2) ^ (2⁻¹ : ℂ) = w
  rw [heq]
  exact Complex.sq_cpow_two_inv hw

end DirichletL
