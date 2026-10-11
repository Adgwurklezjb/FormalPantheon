import Analysis.ContourHalfPlaneRoot
import Analysis.Contours

/-!
The inverse in CDT v2 Appendix equation `firstgobble`, supplied TeX 9956-9964.
-/

namespace DirichletL

/-- The inverse branch of the rational lune map that vanishes at zero, for `c > 1`. -/
noncomputable def contourLuneMap (c : ℝ) (z : ℂ) : ℂ :=
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  (1 - z) / (2 * (a : ℂ)) * (contourHalfPlaneRoot (a ^ 2) (cayleyMap z) - 1)

theorem lune_factor_mem_Ioo {c : ℝ} (hc : 1 < c) :
    (c ^ 2 - 1) / (c ^ 2 + 1) ∈ Set.Ioo (0 : ℝ) 1 := by
  have hplus : 0 < c ^ 2 + 1 := by positivity
  exact ⟨div_pos (by nlinarith only [hc]) hplus,
    (div_lt_one hplus).mpr (by linarith)⟩

theorem contourLuneMap_zero (c : ℝ) : contourLuneMap c 0 = 0 := by
  simp only [contourLuneMap, cayleyMap_zero, contourHalfPlaneRoot_one, sub_self, mul_zero]

theorem analyticAt_contourLuneMap {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (contourLuneMap c) z := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  have ha : a ∈ Set.Ioo (0 : ℝ) 1 := lune_factor_mem_Ioo hc
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.1.ne'
  have ha2 : a ^ 2 ≤ 1 := by nlinarith only [ha.1, ha.2]
  have hk := (analyticAt_contourHalfPlaneRoot (sq_pos_of_pos ha.1) ha2
    (re_cayleyMap_pos hz)).comp' (analyticAt_cayleyMap hz)
  exact ((analyticAt_const.sub analyticAt_id).div analyticAt_const
    (mul_ne_zero (by norm_num) haC)).mul (hk.sub analyticAt_const)

theorem hasDerivAt_contourLuneMap_zero {c : ℝ} (hc : 1 < c) :
    HasDerivAt (contourLuneMap c) (((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) : ℂ) 0 := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  have ha : a ∈ Set.Ioo (0 : ℝ) 1 := lune_factor_mem_Ioo hc
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.1.ne'
  have hk : HasDerivAt (contourHalfPlaneRoot (a ^ 2)) ((a ^ 2 : ℝ) : ℂ)
      (cayleyMap 0) := by
    simpa only [cayleyMap_zero] using hasDerivAt_contourHalfPlaneRoot_one (a ^ 2)
  have hd := ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hasDerivAt_id 0)).div_const
    (2 * (a : ℂ))
  convert hd.mul ((hk.comp 0 hasDerivAt_cayleyMap_zero).sub_const 1) using 1
  change (a : ℂ) = _
  simp only [Function.comp_apply, Pi.sub_apply, id_eq, cayleyMap_zero, contourHalfPlaneRoot_one,
    sub_self, mul_zero, zero_add, sub_zero, Complex.ofReal_pow]
  field_simp

theorem contourLuneMap_quadratic {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ < 1) :
    (((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) : ℂ) * contourLuneMap c z ^ 2 +
      (1 - z) * contourLuneMap c z -
      (((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) : ℂ) * z = 0 := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  have ha : a ∈ Set.Ioo (0 : ℝ) 1 := lune_factor_mem_Ioo hc
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.1.ne'
  have hz1 : z ≠ 1 := by intro he; simp only [he, norm_one, lt_self_iff_false] at hz
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hk := sq_contourHalfPlaneRoot (a ^ 2) (cayleyMap z)
  have hsq : (1 - z) ^ 2 * contourHalfPlaneRoot (a ^ 2) (cayleyMap z) ^ 2 =
      (1 - z) ^ 2 + 4 * (a : ℂ) ^ 2 * z := by
    rw [hk]
    simp only [cayleyMap, Complex.ofReal_pow]
    field_simp
    ring
  change (a : ℂ) * ((1 - z) / (2 * (a : ℂ)) *
      (contourHalfPlaneRoot (a ^ 2) (cayleyMap z) - 1)) ^ 2 +
    (1 - z) * ((1 - z) / (2 * (a : ℂ)) *
      (contourHalfPlaneRoot (a ^ 2) (cayleyMap z) - 1)) - (a : ℂ) * z = 0
  field_simp
  linear_combination hsq

theorem contourLuneMap_add_factor_ne_zero {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ < 1) :
    contourLuneMap c z + (((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) : ℂ) ≠ 0 := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  have ha : a ∈ Set.Ioo (0 : ℝ) 1 := lune_factor_mem_Ioo hc
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.1.ne'
  have ham : (a : ℂ) - 1 ≠ 0 := by exact_mod_cast (sub_ne_zero.mpr ha.2.ne)
  have hap : (a : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith only [ha.1] : a + 1 ≠ 0)
  intro hzero
  have he : contourLuneMap c z = -(a : ℂ) := by linear_combination hzero
  have hq := contourLuneMap_quadratic hc hz
  change (a : ℂ) * contourLuneMap c z ^ 2 + (1 - z) * contourLuneMap c z -
    (a : ℂ) * z = 0 at hq
  rw [he] at hq
  have hf : (a : ℂ) * ((a : ℂ) - 1) * ((a : ℂ) + 1) = 0 := by
    linear_combination hq
  exact mul_ne_zero (mul_ne_zero haC ham) hap hf

theorem luneMap_contourLuneMap {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ < 1) :
    luneMap (c : ℂ) (contourLuneMap c z) = z := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  have hA : c ^ 2 + 1 ≠ 0 := by positivity
  have hAC : (c : ℂ) ^ 2 + 1 ≠ 0 := by exact_mod_cast hA
  have hnorm := contourLuneMap_add_factor_ne_zero hc hz
  have ha : (a : ℂ) * ((c : ℂ) ^ 2 + 1) = (c : ℂ) ^ 2 - 1 := by
    dsimp only [a]
    push_cast
    field_simp
  have hden : ((c : ℂ) ^ 2 - 1) + ((c : ℂ) ^ 2 + 1) * contourLuneMap c z ≠ 0 := by
    have hfactor : ((c : ℂ) ^ 2 - 1) + ((c : ℂ) ^ 2 + 1) * contourLuneMap c z =
        ((c : ℂ) ^ 2 + 1) * (contourLuneMap c z + (a : ℂ)) := by
      linear_combination -ha
    rw [hfactor]
    exact mul_ne_zero hAC hnorm
  apply (div_eq_iff hden).mpr
  have hq := contourLuneMap_quadratic hc hz
  change (a : ℂ) * contourLuneMap c z ^ 2 + (1 - z) * contourLuneMap c z -
    (a : ℂ) * z = 0 at hq
  linear_combination ((c : ℂ) ^ 2 + 1) * hq -
    (contourLuneMap c z ^ 2 - z) * ha

theorem norm_contourLuneMap_lt_one {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖contourLuneMap c z‖ < 1 := by
  have htz : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(t : ℂ) * z‖ < 1 := by
    intro t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg z)).trans_lt (by simpa using hz)
  let g : ℝ → ℝ := fun t => ‖contourLuneMap c ((t : ℂ) * z)‖
  have hg : ContinuousOn g (Set.Icc 0 1) := by
    intro t ht
    have hpath : ContinuousAt (fun u : ℝ => (u : ℂ) * z) t := by fun_prop
    exact (((analyticAt_contourLuneMap hc (htz t ht)).continuousAt.comp
      (f := fun u : ℝ => (u : ℂ) * z) hpath).norm).continuousWithinAt
  by_contra hlt
  have hmem : (1 : ℝ) ∈ Set.Icc (g 0) (g 1) := by
    simpa only [g, Complex.ofReal_zero, Complex.ofReal_one, zero_mul, one_mul,
      contourLuneMap_zero, norm_zero, Set.mem_Icc] using
      (show 0 ≤ (1 : ℝ) ∧ 1 ≤ ‖contourLuneMap c z‖ from ⟨by norm_num, le_of_not_gt hlt⟩)
  obtain ⟨t, ht, htval⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hg hmem
  have hu : ‖contourLuneMap c ((t : ℂ) * z)‖ = 1 := htval
  have hforward := norm_luneMap_ofReal_of_norm_eq_one hc hu
  rw [luneMap_contourLuneMap hc (htz t ht)] at hforward
  exact (ne_of_lt (htz t ht)) hforward

theorem injOn_contourLuneMap {c : ℝ} (hc : 1 < c) :
    Set.InjOn (contourLuneMap c) (Metric.ball (0 : ℂ) 1) := by
  intro z hz w hw he
  have hz1 : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hw1 : ‖w‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hf := congrArg (luneMap (c : ℂ)) he
  simpa only [luneMap_contourLuneMap hc hz1, luneMap_contourLuneMap hc hw1] using hf

end DirichletL
