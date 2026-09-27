import Analysis.ContourLune

/-!
The local rational lune inverse for CDT author Appendix A.4, page 204.
Meanings and pole checks precede these bodies in
-/

namespace DirichletL

theorem luneMap_ofReal_eq (c : ℝ) (z : ℂ) :
    luneMap (c : ℂ) z =
      z * (1 + (((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) : ℂ) * z) /
        ((((c ^ 2 - 1) / (c ^ 2 + 1) : ℝ) : ℂ) + z) := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  have hC : (c : ℂ) ^ 2 + 1 ≠ 0 := by
    exact_mod_cast (show c ^ 2 + 1 ≠ 0 by positivity)
  have ha : (a : ℂ) * ((c : ℂ) ^ 2 + 1) = (c : ℂ) ^ 2 - 1 := by
    dsimp only [a]
    push_cast
    field_simp
  calc
    luneMap (c : ℂ) z =
        (((c : ℂ) ^ 2 + 1) * (z * (1 + (a : ℂ) * z))) /
          (((c : ℂ) ^ 2 + 1) * ((a : ℂ) + z)) := by
      rw [luneMap, ← ha]
      congr 1 <;> ring
    _ = _ := mul_div_mul_left _ _ hC

theorem norm_luneMap_ofReal_le_two_mul {c : ℝ} (hc : 1 < c)
    (ha : (9 / 10 : ℝ) ≤ (c ^ 2 - 1) / (c ^ 2 + 1))
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 10) :
    ‖luneMap (c : ℂ) z‖ ≤ 2 * ‖z‖ := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  have ha01 : a ∈ Set.Ioo (0 : ℝ) 1 := lune_factor_mem_Ioo hc
  have hanorm : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha01.1]
  have hnum : ‖1 + (a : ℂ) * z‖ ≤ 11 / 10 := by
    have htri := norm_add_le (1 : ℂ) ((a : ℂ) * z)
    rw [norm_one, norm_mul, hanorm] at htri
    have hmul := mul_le_mul_of_nonneg_right ha01.2.le (norm_nonneg z)
    nlinarith only [htri, hmul, hz]
  have hden : (4 / 5 : ℝ) ≤ ‖(a : ℂ) + z‖ := by
    have htri := norm_sub_norm_le (a : ℂ) (-z)
    rw [sub_neg_eq_add, norm_neg, hanorm] at htri
    linarith only [htri, ha, hz]
  calc
    ‖luneMap (c : ℂ) z‖ = ‖z‖ * ‖1 + (a : ℂ) * z‖ / ‖(a : ℂ) + z‖ := by
      rw [luneMap_ofReal_eq, norm_div, norm_mul]
    _ ≤ ‖z‖ * (11 / 10) / ‖(a : ℂ) + z‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (norm_nonneg z))
        (norm_nonneg _)
    _ ≤ ‖z‖ * (11 / 10) / (4 / 5) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ ≤ 2 * ‖z‖ := by nlinarith only [norm_nonneg z]

theorem contourLuneMap_luneMap {c : ℝ} (hc : 1 < c) {z : ℂ}
    (hz : ‖z‖ < (c ^ 2 - 1) / (c ^ 2 + 1))
    (himage : ‖luneMap (c : ℂ) z‖ < 1) :
    contourLuneMap c (luneMap (c : ℂ) z) = z := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  let u : ℂ := contourLuneMap c (luneMap (c : ℂ) z)
  have ha : a ∈ Set.Ioo (0 : ℝ) 1 := lune_factor_mem_Ioo hc
  have hz1 : ‖z‖ < 1 := hz.trans ha.2
  have hu : ‖u‖ < 1 := norm_contourLuneMap_lt_one hc himage
  have huz : luneMap (c : ℂ) u = luneMap (c : ℂ) z :=
    luneMap_contourLuneMap hc himage
  have hu0 : (a : ℂ) + u ≠ 0 := by
    simpa only [add_comm] using contourLuneMap_add_factor_ne_zero hc himage
  have hz0 : (a : ℂ) + z ≠ 0 := by
    intro h
    have he : z = -(a : ℂ) := by linear_combination h
    rw [he, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha.1] at hz
    exact lt_irrefl _ hz
  rw [luneMap_ofReal_eq, luneMap_ofReal_eq] at huz
  have heq := (div_eq_div_iff hu0 hz0).mp huz
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha.1.ne'
  have hfactor : (a : ℂ) * ((u - z) * (u * z + (a : ℂ) * (u + z) + 1)) = 0 := by
    linear_combination heq
  have hcases := mul_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left haC)
  rcases hcases with he | he
  · exact sub_eq_zero.mp he
  · have hs : ‖1 + (a : ℂ) * z‖ ^ 2 - ‖(a : ℂ) + z‖ ^ 2 =
        (1 - a ^ 2) * (1 - ‖z‖ ^ 2) := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
        Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hp : 0 < (1 - a ^ 2) * (1 - ‖z‖ ^ 2) :=
      mul_pos (by nlinarith only [ha.1, ha.2])
        (by nlinarith only [hz1, norm_nonneg z])
    have hnorm : ‖(a : ℂ) + z‖ < ‖1 + (a : ℂ) * z‖ := by
      nlinarith only [hs, hp, norm_nonneg ((a : ℂ) + z), norm_nonneg (1 + (a : ℂ) * z)]
    have hbad : ‖((a : ℂ) + z) * u‖ < ‖1 + (a : ℂ) * z‖ := by
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hu.le).trans_lt hnorm
    have he' : ((a : ℂ) + z) * u = -(1 + (a : ℂ) * z) := by
      linear_combination he
    rw [he', norm_neg] at hbad
    exact (lt_irrefl _ hbad).elim

end DirichletL
