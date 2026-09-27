import Analysis.ContourSlitInverse

/-!
Local inverse estimates for the slit factors of CDT author Appendix A.3-A.4,
pages 203-204. Meanings and branch checks precede these bodies in
-/

namespace DirichletL

theorem re_contourHalfPlaneRoot_nonneg (d : ℝ) (w : ℂ) :
    0 ≤ (contourHalfPlaneRoot d w).re := by
  rw [contourHalfPlaneRoot, Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem one_le_norm_contourHalfPlaneRoot_add_one (d : ℝ) (w : ℂ) :
    1 ≤ ‖contourHalfPlaneRoot d w + 1‖ := by
  have hr := re_contourHalfPlaneRoot_nonneg d w
  have hn := Complex.re_le_norm (contourHalfPlaneRoot d w + 1)
  simp only [Complex.add_re, Complex.one_re] at hn
  linarith only [hr, hn]

theorem contourSlitMap_contourSlitInverse {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    contourSlitMap r (contourSlitInverse r z) = z := by
  let d : ℝ := 4 * r / (1 + r) ^ 2
  have hd : d ≠ 0 := (slit_factor_mem_Ioo hr hr1).1.ne'
  have hden : contourHalfPlaneRoot d⁻¹ (cayleyMap z) + 1 ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one
      (one_le_norm_contourHalfPlaneRoot_add_one d⁻¹ (cayleyMap z)))
  have hinv : contourHalfPlaneRoot d (contourHalfPlaneRoot d⁻¹ (cayleyMap z)) =
      cayleyMap z := by
    simpa only [inv_inv] using contourHalfPlaneRoot_inv (inv_ne_zero hd) (re_cayleyMap_pos hz)
  have hz1 : z ≠ 1 := by intro he; simp only [he, norm_one, lt_self_iff_false] at hz
  change inverseCayleyMap (contourHalfPlaneRoot d
    (cayleyMap (inverseCayleyMap (contourHalfPlaneRoot d⁻¹ (cayleyMap z))))) = z
  rw [cayleyMap_inverseCayleyMap hden, hinv, inverseCayleyMap_cayleyMap hz1]

theorem norm_contourSlitInverse_le_six_mul {r : ℝ}
    (hr : (9 / 10 : ℝ) ≤ 4 * r / (1 + r) ^ 2) {z : ℂ} (hz : ‖z‖ ≤ 1 / 10) :
    ‖contourSlitInverse r z‖ ≤ 6 * ‖z‖ := by
  let d : ℝ := 4 * r / (1 + r) ^ 2
  let e : ℝ := d⁻¹
  let k : ℂ := contourHalfPlaneRoot e (cayleyMap z)
  have hd : 0 < d := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 9 / 10) hr
  have he : 0 ≤ e := (inv_pos.mpr hd).le
  have he1 : e ≤ 10 / 9 := by
    convert one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9 / 10) hr using 1 <;>
      norm_num [e, d]
  have hk : 1 ≤ ‖k + 1‖ := one_le_norm_contourHalfPlaneRoot_add_one e (cayleyMap z)
  have hz1 : z ≠ 1 := by intro h; simp only [h, norm_one] at hz; norm_num at hz
  have hzden : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hfactor : (k - 1) * (k + 1) = (e : ℂ) * (4 * z / (1 - z) ^ 2) := by
    calc
      _ = k ^ 2 - 1 := by ring
      _ = (1 - (e : ℂ)) + (e : ℂ) * cayleyMap z ^ 2 - 1 := by
        dsimp only [k]
        rw [sq_contourHalfPlaneRoot]
      _ = _ := by
        dsimp only [cayleyMap]
        field_simp
        ring
  have hnorm : ‖k - 1‖ * ‖k + 1‖ = e * (4 * ‖z‖ / ‖1 - z‖ ^ 2) := by
    rw [← norm_mul, hfactor, norm_mul, norm_div, norm_mul, norm_pow]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
  have hlow : (9 / 10 : ℝ) ≤ ‖1 - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at h
    linarith only [hz, h]
  have hlow2 : (81 / 100 : ℝ) ≤ ‖1 - z‖ ^ 2 := by nlinarith only [hlow]
  have hquot : 4 * ‖z‖ / ‖1 - z‖ ^ 2 ≤ 4 * ‖z‖ / (81 / 100) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hlow2
  calc
    ‖contourSlitInverse r z‖ = ‖k - 1‖ / ‖k + 1‖ := by
      rw [contourSlitInverse, inverseCayleyMap, norm_div]
    _ ≤ ‖k - 1‖ := div_le_self (norm_nonneg _) hk
    _ ≤ ‖k - 1‖ * ‖k + 1‖ := le_mul_of_one_le_right (norm_nonneg _) hk
    _ = e * (4 * ‖z‖ / ‖1 - z‖ ^ 2) := hnorm
    _ ≤ (10 / 9) * (4 * ‖z‖ / (81 / 100)) :=
      mul_le_mul he1 hquot (by positivity) (by norm_num)
    _ ≤ 6 * ‖z‖ := by nlinarith only [norm_nonneg z]

end DirichletL
