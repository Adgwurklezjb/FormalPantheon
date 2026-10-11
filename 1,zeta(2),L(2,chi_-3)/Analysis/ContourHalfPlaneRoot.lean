import Analysis.ContourCayley

/-!
The normalized branch for CDT v2's slit map, TeX 10003-10019.
-/

namespace DirichletL

/-- The principal square root of `(1-d)+d*w^2`, normalized to one at `w=1`. -/
noncomputable def contourHalfPlaneRoot (d : ℝ) (w : ℂ) : ℂ :=
  ((1 - (d : ℂ)) + (d : ℂ) * w ^ 2) ^ (2⁻¹ : ℂ)

theorem sq_contourHalfPlaneRoot (d : ℝ) (w : ℂ) :
    contourHalfPlaneRoot d w ^ 2 = (1 - (d : ℂ)) + (d : ℂ) * w ^ 2 :=
  Complex.cpow_ofNat_inv_pow _ 2

theorem contourHalfPlaneRoot_one (d : ℝ) : contourHalfPlaneRoot d 1 = 1 := by
  simp [contourHalfPlaneRoot]

theorem halfPlane_mix_mem_slitPlane {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    {w : ℂ} (hw : 0 < w.re) :
    (1 - (d : ℂ)) + (d : ℂ) * w ^ 2 ∈ Complex.slitPlane := by
  change 0 < ((1 - (d : ℂ)) + (d : ℂ) * w ^ 2).re ∨
    ((1 - (d : ℂ)) + (d : ℂ) * w ^ 2).im ≠ 0
  rcases eq_or_ne w.im 0 with him | him
  · left
    simp only [pow_two, Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, him,
      mul_zero, zero_mul, sub_zero]
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hd1) (mul_pos hd (mul_pos hw hw))
  · right
    have hi : d * (2 * w.re * w.im) ≠ 0 :=
      mul_ne_zero hd.ne' (mul_ne_zero (mul_ne_zero (by norm_num) hw.ne') him)
    convert hi using 1
    simp only [pow_two, Complex.add_im, Complex.sub_im, Complex.one_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

theorem re_cpow_inv_two_pos {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < (z ^ (2⁻¹ : ℂ)).re := by
  rw [Complex.cpow_inv_two_re, Real.sqrt_pos]
  apply div_pos _ (by norm_num)
  rcases hz with hre | him
  · exact add_pos_of_nonneg_of_pos (norm_nonneg z) hre
  · have hnorm := Complex.abs_re_lt_norm.mpr him
    linarith only [hnorm, neg_le_abs z.re]

theorem re_contourHalfPlaneRoot_pos {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    {w : ℂ} (hw : 0 < w.re) : 0 < (contourHalfPlaneRoot d w).re :=
  re_cpow_inv_two_pos (halfPlane_mix_mem_slitPlane hd hd1 hw)

theorem analyticAt_contourHalfPlaneRoot {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    {w : ℂ} (hw : 0 < w.re) : AnalyticAt ℂ (contourHalfPlaneRoot d) w := by
  exact (analyticAt_const.add (analyticAt_const.mul (analyticAt_id.fun_pow 2))).cpow
    analyticAt_const (halfPlane_mix_mem_slitPlane hd hd1 hw)

theorem hasDerivAt_contourHalfPlaneRoot_one (d : ℝ) :
    HasDerivAt (contourHalfPlaneRoot d) (d : ℂ) 1 := by
  have hp : HasDerivAt (fun w : ℂ => (1 - (d : ℂ)) + (d : ℂ) * w ^ 2)
      (2 * (d : ℂ)) 1 := by
    convert (((hasDerivAt_id (𝕜 := ℂ) 1).pow 2).const_mul (d : ℂ)).const_add
      (1 - (d : ℂ)) using 1
    norm_num
    ring
  have harg : (1 - (d : ℂ)) + (d : ℂ) * (1 : ℂ) ^ 2 ∈ Complex.slitPlane := by simp
  convert hp.cpow_const (c := (2⁻¹ : ℂ)) harg using 1
  norm_num [contourHalfPlaneRoot]
  ring

theorem injOn_contourHalfPlaneRoot {d : ℝ} (hd : 0 < d) :
    Set.InjOn (contourHalfPlaneRoot d) {w : ℂ | 0 < w.re} := by
  intro z hz w hw he
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hs := congrArg (fun u : ℂ => u ^ 2) he
  dsimp only at hs
  rw [sq_contourHalfPlaneRoot, sq_contourHalfPlaneRoot] at hs
  have hc : (d : ℂ) * (z ^ 2 - w ^ 2) = 0 := by linear_combination hs
  have hsquare := (mul_eq_zero.mp hc).resolve_left hdC
  have hfactor : (z - w) * (z + w) = 0 := by linear_combination hsquare
  rcases mul_eq_zero.mp hfactor with hsub | hadd
  · exact sub_eq_zero.mp hsub
  · have hre := congrArg Complex.re hadd
    simp only [Complex.add_re, Complex.zero_re] at hre
    change 0 < z.re at hz
    change 0 < w.re at hw
    linarith only [hz, hw, hre]

end DirichletL
