import Mathlib

/-!
The half-plane transformations in CDT v2 Appendix subsection `Slits`, TeX 10003-10019.
-/

namespace DirichletL

/-- The Cayley transform from the open unit disc to the right half-plane. -/
noncomputable def cayleyMap (z : ℂ) : ℂ := (1 + z) / (1 - z)

/-- The inverse Cayley transform on the right half-plane. -/
noncomputable def inverseCayleyMap (w : ℂ) : ℂ := (w - 1) / (w + 1)

theorem cayleyMap_zero : cayleyMap 0 = 1 := by simp [cayleyMap]

theorem inverseCayleyMap_one : inverseCayleyMap 1 = 0 := by simp [inverseCayleyMap]

theorem re_cayleyMap_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < (cayleyMap z).re := by
  have hz1 : z ≠ 1 := by intro he; simp only [he, norm_one, lt_self_iff_false] at hz
  have hden := Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1.symm)
  have hsq : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith only [hz, norm_nonneg z]
  have hid : (cayleyMap z).re = (1 - Complex.normSq z) / Complex.normSq (1 - z) := by
    simp only [cayleyMap, Complex.div_re, Complex.add_re, Complex.sub_re,
      Complex.add_im, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.normSq_apply]
    ring
  rw [hid]
  exact div_pos (sub_pos.mpr hsq) hden

theorem norm_inverseCayleyMap_lt_one {w : ℂ} (hw : 0 < w.re) :
    ‖inverseCayleyMap w‖ < 1 := by
  have hden : w + 1 ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith only [hw, hre]
  have hsq : ‖w - 1‖ ^ 2 < ‖w + 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_sub, Complex.normSq_add, Complex.normSq_one, map_one, mul_one]
    linarith only [hw]
  rw [inverseCayleyMap, norm_div]
  apply (div_lt_one (norm_pos_iff.mpr hden)).mpr
  nlinarith only [hsq, norm_nonneg (w - 1), norm_nonneg (w + 1)]

theorem analyticAt_cayleyMap {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ cayleyMap z := by
  have hz1 : z ≠ 1 := by intro he; simp only [he, norm_one, lt_self_iff_false] at hz
  exact (analyticAt_const.add analyticAt_id).div (analyticAt_const.sub analyticAt_id)
    (sub_ne_zero.mpr hz1.symm)

theorem analyticAt_inverseCayleyMap {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ inverseCayleyMap w := by
  have hden : w + 1 ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith only [hw, hre]
  exact (analyticAt_id.sub analyticAt_const).div (analyticAt_id.add analyticAt_const) hden

theorem hasDerivAt_cayleyMap_zero : HasDerivAt cayleyMap 2 0 := by
  convert ((hasDerivAt_id (𝕜 := ℂ) 0).const_add 1).div
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hasDerivAt_id 0)) (by norm_num) using 1
  norm_num [cayleyMap]

theorem hasDerivAt_inverseCayleyMap_one : HasDerivAt inverseCayleyMap (1 / 2) 1 := by
  convert ((hasDerivAt_id (𝕜 := ℂ) 1).sub_const 1).div
    ((hasDerivAt_id (𝕜 := ℂ) 1).add_const 1) (by norm_num) using 1
  norm_num [inverseCayleyMap]

theorem injOn_cayleyMap : Set.InjOn cayleyMap (Metric.ball (0 : ℂ) 1) := by
  intro z hz w hw he
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have hw1 : w ≠ 1 := by intro h; simp [h] at hw
  have hc := (div_eq_div_iff (sub_ne_zero.mpr hz1.symm)
    (sub_ne_zero.mpr hw1.symm)).mp he
  linear_combination (1 / 2 : ℂ) * hc

theorem injOn_inverseCayleyMap : Set.InjOn inverseCayleyMap {w : ℂ | 0 < w.re} := by
  intro z hz w hw he
  have hzne : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    change 0 < z.re at hz
    linarith only [hz, hre]
  have hwne : w + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    change 0 < w.re at hw
    linarith only [hw, hre]
  have hc := (div_eq_div_iff hzne hwne).mp he
  linear_combination (1 / 2 : ℂ) * hc

end DirichletL
