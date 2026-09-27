import Analysis.ContourDiskMap
import Analysis.LevelTwoHauptmodul

/-!
The contour phi in the CDT author revision of 2026-09-02, Appendix A.4, pages 204-205.
Only its analytic and derivative properties are proved here; its exceptional
fiber is a separate obligation. Meanings precede these bodies in
-/

namespace DirichletL

/-- The holonomy contour obtained by composing CDT's disc map with the level-two product. -/
noncomputable def cdtContourMap (z : ℂ) : ℂ := levelTwoHauptmodul (cdtContourDiskMap z)

theorem cdtContourMap_zero : cdtContourMap 0 = 0 := by
  rw [cdtContourMap, cdtContourDiskMap_zero, levelTwoHauptmodul_zero]

theorem analyticOnNhd_cdtContourMap :
    AnalyticOnNhd ℂ cdtContourMap (Metric.closedBall 0 1) := by
  intro z hz
  have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hG : cdtContourDiskMap z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact (norm_cdtContourDiskMap_lt hz1).trans (by norm_num)
  exact (analyticOnNhd_levelTwoHauptmodul _ hG).comp' (analyticOnNhd_cdtContourDiskMap _ hz)

theorem norm_deriv_cdtContourMap_zero :
    ‖deriv cdtContourMap 0‖ = 256 * cdtContourConformalRadius := by
  have hG := (analyticOnNhd_cdtContourDiskMap 0 (by simp)).differentiableAt.hasDerivAt
  have hh : HasDerivAt levelTwoHauptmodul (-256) (cdtContourDiskMap 0) := by
    simpa only [cdtContourDiskMap_zero] using hasDerivAt_levelTwoHauptmodul_zero
  have hφ := hh.comp 0 hG
  change HasDerivAt cdtContourMap _ 0 at hφ
  rw [hφ.deriv, norm_mul, norm_deriv_cdtContourDiskMap_zero]
  norm_num

theorem cdtContourMap_eq_zero_iff {z : ℂ} (hz : ‖z‖ ≤ 1) :
    cdtContourMap z = 0 ↔ z = 0 := by
  constructor
  · intro he
    have hG : ‖cdtContourDiskMap z‖ < 1 :=
      (norm_cdtContourDiskMap_lt hz).trans (by norm_num)
    have hzero : cdtContourDiskMap z = 0 := by
      by_contra hne
      exact (levelTwoHauptmodul_ne_zero_iff hG).mpr hne he
    apply injOn_cdtContourDiskMap (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz)
      (by simp)
    simpa only [cdtContourDiskMap_zero] using hzero
  · rintro rfl
    exact cdtContourMap_zero

end DirichletL
