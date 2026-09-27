import Analysis.ContourHalfPlaneRoot

/-!
The normalized slit map in CDT v2 TeX 10003-10019, composed without a quotient at zero.
-/

namespace DirichletL

/-- The normalized slit branch in Cayley coordinates, with derivative `4*r/(1+r)^2`. -/
noncomputable def contourSlitMap (r : ℝ) (z : ℂ) : ℂ :=
  inverseCayleyMap (contourHalfPlaneRoot (4 * r / (1 + r) ^ 2) (cayleyMap z))

theorem slit_factor_mem_Ioo {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    4 * r / (1 + r) ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  refine ⟨by positivity, ?_⟩
  apply (div_lt_one (sq_pos_of_pos (by linarith : 0 < 1 + r))).mpr
  nlinarith only [sq_pos_of_pos (sub_pos.mpr hr1)]

theorem contourSlitMap_zero (r : ℝ) : contourSlitMap r 0 = 0 := by
  rw [contourSlitMap, cayleyMap_zero, contourHalfPlaneRoot_one, inverseCayleyMap_one]

theorem analyticAt_contourSlitMap {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ (contourSlitMap r) z := by
  have hd := slit_factor_mem_Ioo hr hr1
  have hw := re_cayleyMap_pos hz
  exact ((analyticAt_inverseCayleyMap (re_contourHalfPlaneRoot_pos hd.1 hd.2.le hw)).comp'
    (analyticAt_contourHalfPlaneRoot hd.1 hd.2.le hw)).comp' (analyticAt_cayleyMap hz)

theorem norm_contourSlitMap_lt_one {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖contourSlitMap r z‖ < 1 := by
  have hd := slit_factor_mem_Ioo hr hr1
  exact norm_inverseCayleyMap_lt_one
    (re_contourHalfPlaneRoot_pos hd.1 hd.2.le (re_cayleyMap_pos hz))

theorem hasDerivAt_contourSlitMap_zero (r : ℝ) :
    HasDerivAt (contourSlitMap r) ((4 * r / (1 + r) ^ 2 : ℝ) : ℂ) 0 := by
  let d : ℝ := 4 * r / (1 + r) ^ 2
  have hk : HasDerivAt (contourHalfPlaneRoot d) (d : ℂ) (cayleyMap 0) := by
    simpa only [cayleyMap_zero] using hasDerivAt_contourHalfPlaneRoot_one d
  have hc := hk.comp 0 hasDerivAt_cayleyMap_zero
  have hi : HasDerivAt inverseCayleyMap (1 / 2 : ℂ)
      (contourHalfPlaneRoot d (cayleyMap 0)) := by
    simpa only [cayleyMap_zero, contourHalfPlaneRoot_one] using hasDerivAt_inverseCayleyMap_one
  convert hi.comp 0 hc using 1
  dsimp only [contourSlitMap, d, Function.comp_def]
  ring

theorem injOn_contourSlitMap {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    Set.InjOn (contourSlitMap r) (Metric.ball (0 : ℂ) 1) := by
  have hd := slit_factor_mem_Ioo hr hr1
  intro z hz w hw he
  have hz1 : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hw1 : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  apply injOn_cayleyMap hz hw
  apply injOn_contourHalfPlaneRoot hd.1 (re_cayleyMap_pos hz1) (re_cayleyMap_pos hw1)
  apply injOn_inverseCayleyMap
    (re_contourHalfPlaneRoot_pos hd.1 hd.2.le (re_cayleyMap_pos hz1))
    (re_contourHalfPlaneRoot_pos hd.1 hd.2.le (re_cayleyMap_pos hw1))
  exact he

end DirichletL
