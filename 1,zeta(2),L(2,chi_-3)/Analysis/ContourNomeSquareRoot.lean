import Analysis.ContourDiskMap
import Analysis.AnalyticSquareRootsOnBalls

/-!
An odd analytic square root of the contour nome after doubling the parameter.
Source: CDT v2 TeX 7157-7173 and author revision 2026-09-02, Appendix A.4.
Prior meanings and the removable zero check:
-/

namespace DirichletL

open scoped Topology

theorem analyticOnNhd_dslope_cdtContourDiskMap :
    AnalyticOnNhd ℂ (dslope cdtContourDiskMap 0) (Metric.ball 0 1) := by
  have hG := analyticOnNhd_cdtContourDiskMap.differentiableOn.mono
    Metric.ball_subset_closedBall
  exact ((Complex.differentiableOn_dslope
    (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1))).mpr hG).analyticOnNhd
      Metric.isOpen_ball

theorem dslope_cdtContourDiskMap_ne_zero {z : ℂ} (hz : ‖z‖ < 1) :
    dslope cdtContourDiskMap 0 z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst z
    rw [dslope_same]
    apply norm_pos_iff.mp
    rw [norm_deriv_cdtContourDiskMap_zero]
    linarith [cdtContourConformalRadius_gt_half]
  · intro he
    have h := sub_smul_dslope cdtContourDiskMap 0 z
    simp only [sub_zero, he, smul_zero, cdtContourDiskMap_zero] at h
    apply hz0
    exact injOn_cdtContourDiskMap (by simpa using hz.le) (by simp)
      (h.symm.trans cdtContourDiskMap_zero.symm)

theorem exists_analytic_cdtContourNome_square_root :
    ∃ t : ℂ → ℂ, AnalyticOnNhd ℂ t (Metric.ball 0 1) ∧ t 0 = 0 ∧
      (∀ z : ℂ, t (-z) = -t z) ∧
      ∀ z : ℂ, ‖z‖ < 1 → t z ^ 2 = cdtContourDiskMap (z ^ 2) := by
  let g := dslope cdtContourDiskMap 0
  have hs : (g 0 ^ (1 / 2 : ℂ)) ^ 2 = g 0 := by
    simpa only [one_div] using Complex.cpow_nat_inv_pow (g 0) (n := 2) two_ne_zero
  obtain ⟨S, hSa, _, hSs⟩ := exists_analytic_square_root_on_ball
    (by norm_num : (0 : ℝ) < 1) analyticOnNhd_dslope_cdtContourDiskMap
    (fun z hz => dslope_cdtContourDiskMap_ne_zero (by simpa using hz)) hs
  have hsq (z : ℂ) (hz : ‖z‖ < 1) : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  refine ⟨fun z => z * S (z ^ 2), ?_, by simp, ?_, ?_⟩
  · intro z hz
    have hz' : z ^ 2 ∈ Metric.ball (0 : ℂ) 1 := by
      simpa using hsq z (by simpa using hz)
    exact analyticAt_id.mul ((hSa _ hz').comp'
      (f := fun w : ℂ => w ^ 2) (analyticAt_id.pow 2))
  · intro z
    simp only [neg_sq, neg_mul]
  · intro z hz
    rw [mul_pow, hSs _ (by simpa using hsq z hz)]
    simpa only [sub_zero, cdtContourDiskMap_zero, smul_eq_mul] using
      sub_smul_dslope cdtContourDiskMap 0 (z ^ 2)

end DirichletL
