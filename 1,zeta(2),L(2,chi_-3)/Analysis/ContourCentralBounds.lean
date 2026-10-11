import Analysis.ContourExceptionalUniqueness
import Analysis.ContourSlitLocalInverse
import Analysis.ContourLuneLocalInverse

/-!
Quantitative central bounds for the continuation argument of CDT v2,
TeX 1739-1744 and 7157-7173, using author Appendix A.4, pages 203-205.
-/

namespace DirichletL

theorem norm_contourSlitInverse_le_six_fifths_mul {r : ℝ}
    (hr : (9 / 10 : ℝ) ≤ 4 * r / (1 + r) ^ 2)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 100) :
    ‖contourSlitInverse r z‖ ≤ (6 / 5 : ℝ) * ‖z‖ := by
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
  have hlow : (99 / 100 : ℝ) ≤ ‖1 - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at h
    linarith only [hz, h]
  have hlow2 : (99 / 100 : ℝ) ^ 2 ≤ ‖1 - z‖ ^ 2 := by nlinarith only [hlow]
  have hquot : 4 * ‖z‖ / ‖1 - z‖ ^ 2 ≤ 4 * ‖z‖ / (99 / 100) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hlow2
  have hprod : ‖k - 1‖ * ‖k + 1‖ ≤ (10 / 9) * (4 * ‖z‖ / (99 / 100) ^ 2) := by
    rw [hnorm]
    exact mul_le_mul he1 hquot (by positivity) (by norm_num)
  have hsmall : ‖k - 1‖ ≤ 1 / 20 := by
    have h := le_mul_of_one_le_right (norm_nonneg (k - 1)) hk
    norm_num [div_eq_mul_inv] at hprod ⊢
    nlinarith only [h, hprod, hz]
  have hkstrong : (39 / 20 : ℝ) ≤ ‖k + 1‖ := by
    have h := norm_add_le (k + 1) (1 - k)
    rw [show k + 1 + (1 - k) = (2 : ℂ) by ring, norm_sub_rev 1 k] at h
    norm_num at h
    linarith only [h, hsmall]
  have hminus : ‖k - 1‖ ≤ ((10 / 9) * (4 * ‖z‖ / (99 / 100) ^ 2)) / (39 / 20) := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 39 / 20)).mpr
    exact (mul_le_mul_of_nonneg_left hkstrong (norm_nonneg _)).trans hprod
  calc
    ‖contourSlitInverse r z‖ = ‖k - 1‖ / ‖k + 1‖ := by
      rw [contourSlitInverse, inverseCayleyMap, norm_div]
    _ ≤ ‖k - 1‖ / (39 / 20) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hkstrong
    _ ≤ (((10 / 9) * (4 * ‖z‖ / (99 / 100) ^ 2)) / (39 / 20)) / (39 / 20) :=
      div_le_div_of_nonneg_right hminus (by norm_num)
    _ ≤ (6 / 5) * ‖z‖ := by
      norm_num [div_eq_mul_inv]
      nlinarith only [norm_nonneg z]

theorem norm_luneMap_ofReal_le_six_fifths_mul {c : ℝ} (hc : 1 < c)
    (ha : (9 / 10 : ℝ) ≤ (c ^ 2 - 1) / (c ^ 2 + 1))
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 100) :
    ‖luneMap (c : ℂ) z‖ ≤ (6 / 5 : ℝ) * ‖z‖ := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  have ha01 : a ∈ Set.Ioo (0 : ℝ) 1 := lune_factor_mem_Ioo hc
  have hanorm : ‖(a : ℂ)‖ = a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha01.1]
  have hnum : ‖1 + (a : ℂ) * z‖ ≤ 101 / 100 := by
    have htri := norm_add_le (1 : ℂ) ((a : ℂ) * z)
    rw [norm_one, norm_mul, hanorm] at htri
    have hmul := mul_le_mul_of_nonneg_right ha01.2.le (norm_nonneg z)
    nlinarith only [htri, hmul, hz]
  have hden : (89 / 100 : ℝ) ≤ ‖(a : ℂ) + z‖ := by
    have htri := norm_sub_norm_le (a : ℂ) (-z)
    rw [sub_neg_eq_add, norm_neg, hanorm] at htri
    linarith only [htri, ha, hz]
  calc
    ‖luneMap (c : ℂ) z‖ = ‖z‖ * ‖1 + (a : ℂ) * z‖ / ‖(a : ℂ) + z‖ := by
      rw [luneMap_ofReal_eq, norm_div, norm_mul]
    _ ≤ ‖z‖ * (101 / 100) / ‖(a : ℂ) + z‖ :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (norm_nonneg z))
        (norm_nonneg _)
    _ ≤ ‖z‖ * (101 / 100) / (89 / 100) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ ≤ (6 / 5 : ℝ) * ‖z‖ := by nlinarith only [norm_nonneg z]

theorem norm_cdtContourReverseMap_le_small {q : ℂ} (hq : ‖q‖ ≤ 1 / 10000) :
    ‖cdtContourReverseMap q‖ ≤ (10368 / 3125 : ℝ) * ‖q‖ := by
  let u : ℂ := -(100 / 77 : ℂ) * q
  let v4 : ℂ := -(contourRotation (-783 / 10000))⁻¹ * luneMap ((75 / 10 : ℝ) : ℂ) u
  let v3 : ℂ := (contourRotation (3525 / 100000))⁻¹ * contourSlitInverse (772 / 1000) v4
  let v2 : ℂ := (contourRotation (11543 / 100000))⁻¹ * contourSlitInverse (55515 / 100000) v3
  let v1 : ℂ := (contourRotation (7977 / 100000))⁻¹ * contourSlitInverse (6188 / 10000) v2
  let v0 : ℂ := contourSlitInverse (91 / 100) v1
  have hu : ‖u‖ ≤ (4 / 3) * ‖q‖ := by
    dsimp only [u]
    rw [norm_mul, norm_neg]
    norm_num
    nlinarith only [norm_nonneg q]
  have hu1 : ‖u‖ ≤ 1 / 100 := by linarith only [hu, hq]
  have hL : ‖luneMap ((75 / 10 : ℝ) : ℂ) u‖ ≤ (6 / 5) * ‖u‖ :=
    norm_luneMap_ofReal_le_six_fifths_mul (by norm_num) (by norm_num) hu1
  have h4 : ‖v4‖ ≤ (8 / 5) * ‖q‖ := by
    dsimp only [v4]
    rw [norm_mul, norm_neg, norm_inv, norm_contourRotation, inv_one, one_mul]
    linarith only [hL, hu]
  have h4small : ‖v4‖ ≤ 1 / 100 := by linarith only [h4, hq]
  have h3 : ‖v3‖ ≤ (48 / 25) * ‖q‖ := by
    have h := norm_contourSlitInverse_le_six_fifths_mul (r := 772 / 1000) (by norm_num) h4small
    dsimp only [v3]
    rw [norm_mul, norm_inv, norm_contourRotation, inv_one, one_mul]
    linarith only [h, h4]
  have h3small : ‖v3‖ ≤ 1 / 100 := by linarith only [h3, hq]
  have h2 : ‖v2‖ ≤ (288 / 125) * ‖q‖ := by
    have h := norm_contourSlitInverse_le_six_fifths_mul (r := 55515 / 100000) (by norm_num) h3small
    dsimp only [v2]
    rw [norm_mul, norm_inv, norm_contourRotation, inv_one, one_mul]
    linarith only [h, h3]
  have h2small : ‖v2‖ ≤ 1 / 100 := by linarith only [h2, hq]
  have h1 : ‖v1‖ ≤ (1728 / 625) * ‖q‖ := by
    have h := norm_contourSlitInverse_le_six_fifths_mul (r := 6188 / 10000) (by norm_num) h2small
    dsimp only [v1]
    rw [norm_mul, norm_inv, norm_contourRotation, inv_one, one_mul]
    linarith only [h, h2]
  have h1small : ‖v1‖ ≤ 1 / 100 := by linarith only [h1, hq]
  have h0 : ‖v0‖ ≤ (10368 / 3125) * ‖q‖ := by
    have h := norm_contourSlitInverse_le_six_fifths_mul (r := 91 / 100) (by norm_num) h1small
    change ‖contourSlitInverse (91 / 100) v1‖ ≤ _
    linarith only [h, h1]
  exact h0

theorem norm_lt_one_div_fiveThousand_of_cdtContourMap_eq {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1)
    (hv : cdtContourMap z = -1 / 72) : ‖z‖ < 1 / 5000 := by
  obtain ⟨q, hq, hvq⟩ := exists_levelTwoHauptmodul_eq_neg_one_div_seventyTwo
  have hqnorm : ‖(q : ℂ)‖ ≤ 1 / 10000 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq.1]
    exact hq.2.le
  have hroot := levelTwoHauptmodul_real_preimage_refined_bounds hq hvq
  have hreverse := norm_cdtContourReverseMap_le_small hqnorm
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq.1] at hreverse
  let w : ℂ := (1000 / 995 : ℂ) * cdtContourReverseMap (q : ℂ)
  have hw : ‖w‖ < 1 / 5000 := by
    have hscalar : (1000 / 995 : ℝ) * (10368 / 3125) *
        (5418296542878 / 100000000000000000) < 1 / 5000 := by norm_num
    calc
      ‖w‖ = (1000 / 995 : ℝ) * ‖cdtContourReverseMap (q : ℂ)‖ := by
        dsimp only [w]
        rw [norm_mul]
        norm_num
      _ ≤ (1000 / 995 : ℝ) * ((10368 / 3125) * q) :=
        mul_le_mul_of_nonneg_left hreverse (by norm_num)
      _ ≤ (1000 / 995 : ℝ) * (10368 / 3125) *
          (5418296542878 / 100000000000000000) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hroot.2 (by norm_num)
      _ < 1 / 5000 := hscalar
  have hw1 : w ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact hw.le.trans (by norm_num)
  have hG : cdtContourDiskMap z = (q : ℂ) :=
    levelTwoHauptmodul_eq_real_preimage_of_mem_image hq hvq ⟨z, hz, rfl⟩ hv
  have heq : z = w := injOn_cdtContourDiskMap hz hw1
    (hG.trans (cdtContourReverseMap_spec hqnorm).2.symm)
  simpa only [heq] using hw

theorem norm_cdtContourDiskMap_le_mul {z : ℂ} (hz : ‖z‖ < 1) :
    ‖cdtContourDiskMap z‖ ≤ (77 / 100 : ℝ) * ‖z‖ := by
  have hd : DifferentiableOn ℂ cdtContourDiskMap (Metric.ball 0 1) :=
    (analyticOnNhd_cdtContourDiskMap.mono Metric.ball_subset_closedBall).differentiableOn
  have hm : Set.MapsTo cdtContourDiskMap (Metric.ball 0 1)
      (Metric.ball (cdtContourDiskMap 0) (77 / 100)) := by
    intro w hw
    rw [cdtContourDiskMap_zero, Metric.mem_ball, dist_zero_right]
    exact norm_cdtContourDiskMap_lt
      (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hw))
  have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd hm
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  simpa only [cdtContourDiskMap_zero, dist_zero_right, div_one] using h

end DirichletL
