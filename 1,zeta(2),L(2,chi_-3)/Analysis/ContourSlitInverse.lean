import Analysis.ContourSlit
import Analysis.ContourComponentInverses

/-!
The inverse on the actual image of CDT v2's slit map, supplied TeX 10003-10019.
-/

namespace DirichletL

/-- A total inverse expression for the normalized slit map, valid on its actual disc image. -/
noncomputable def contourSlitInverse (r : ℝ) (z : ℂ) : ℂ :=
  inverseCayleyMap (contourHalfPlaneRoot (4 * r / (1 + r) ^ 2)⁻¹ (cayleyMap z))

theorem contourSlitInverse_zero (r : ℝ) : contourSlitInverse r 0 = 0 := by
  rw [contourSlitInverse, cayleyMap_zero, contourHalfPlaneRoot_one, inverseCayleyMap_one]

theorem contourSlitInverse_contourSlitMap {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ < 1) : contourSlitInverse r (contourSlitMap r z) = z := by
  let d : ℝ := 4 * r / (1 + r) ^ 2
  have hd : d ∈ Set.Ioo (0 : ℝ) 1 := slit_factor_mem_Ioo hr hr1
  have hw := re_cayleyMap_pos hz
  have hK := re_contourHalfPlaneRoot_pos hd.1 hd.2.le hw
  have hden : contourHalfPlaneRoot d (cayleyMap z) + 1 ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith only [hK, hre]
  have hz1 : z ≠ 1 := by intro he; simp only [he, norm_one, lt_self_iff_false] at hz
  change inverseCayleyMap (contourHalfPlaneRoot d⁻¹
    (cayleyMap (inverseCayleyMap (contourHalfPlaneRoot d (cayleyMap z))))) = z
  rw [cayleyMap_inverseCayleyMap hden, contourHalfPlaneRoot_inv hd.1.ne' hw,
    inverseCayleyMap_cayleyMap hz1]

end DirichletL
