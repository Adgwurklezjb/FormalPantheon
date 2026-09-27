import Analysis.LevelTwoLambda

/-!
Exact geometric-series bounds near zero for the original theta coordinate.
Source: CDT v2 TeX 7157-7173; DLMF 20.7.5 with the existing theta convention.
-/

namespace DirichletL

private theorem norm_sub_one_le_of_hasSum_square_majorant
    {u : ℕ → ℂ} {v : ℂ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hu : HasSum u ((v + 1) / 2)) (hu0 : u 0 = 1)
    (hbound : ∀ n, ‖u n‖ ≤ r ^ (n ^ 2)) :
    ‖v - 1‖ ≤ 2 * r / (1 - r) := by
  have htail : HasSum (fun n => u (n + 1)) ((v - 1) / 2) := by
    convert (hasSum_nat_add_iff' 1).mpr hu using 1
    simp only [Finset.sum_range_one, hu0]
    ring
  have hgeom : HasSum (fun n : ℕ => r ^ (n + 1)) (r / (1 - r)) := by
    simpa only [pow_succ, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
  have h := htail.norm_le_of_bounded hgeom (fun n =>
    (hbound (n + 1)).trans (pow_le_pow_of_le_one hr0 hr1.le
      (show n + 1 ≤ (n + 1) ^ 2 by nlinarith)))
  rw [norm_div] at h
  norm_num at h
  rw [mul_div_assoc]
  linarith

theorem norm_sum_complexSeries_thetaThreeSeries_sub_one_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖(complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q - 1‖ ≤
      2 * ‖q‖ / (1 - ‖q‖) := by
  by_cases hq0 : q = 0
  · subst q
    rw [sum_complexSeries_thetaThreeSeries_eq_tprod hq]
    simp [pow_mul]
  · let τ := Function.Periodic.invQParam 1 q
    have hτ : 0 < τ.im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0
    have hqτ : Function.Periodic.qParam 1 τ = q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    have hs := hasSum_qParam_square hτ
    rw [← sum_complexSeries_thetaThreeSeries_qParam hτ, hqτ] at hs
    apply norm_sub_one_le_of_hasSum_square_majorant (norm_nonneg q) hq hs
    · simp
    · intro n
      simp only [norm_pow, le_refl]

theorem norm_sum_complexSeries_thetaFourSeries_sub_one_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖(complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q - 1‖ ≤
      2 * ‖q‖ / (1 - ‖q‖) := by
  by_cases hq0 : q = 0
  · subst q
    rw [sum_complexSeries_thetaFourSeries_eq_tprod hq]
    simp [pow_mul]
  · let τ := Function.Periodic.invQParam 1 q
    have hτ : 0 < τ.im :=
      Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num) hq hq0
    have hqτ : Function.Periodic.qParam 1 τ = q :=
      Function.Periodic.qParam_right_inv (by norm_num) hq0
    have hs := hasSum_neg_one_pow_mul_qParam_square hτ
    rw [← sum_complexSeries_thetaFourSeries_qParam hτ, hqτ] at hs
    apply norm_sub_one_le_of_hasSum_square_majorant (norm_nonneg q) hq hs
    · simp
    · intro n
      simp

theorem norm_levelTwoLambda_lt_half {q : ℂ} (hq : ‖q‖ < 1 / 50) :
    ‖levelTwoLambda q‖ < 1 / 2 := by
  let A := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaThreeSeries)).sum q
  let B := (complexSeries (PowerSeries.map (Int.castRingHom ℚ) thetaFourSeries)).sum q
  have hq1 : ‖q‖ < 1 := hq.trans (by norm_num)
  have hsmall : 2 * ‖q‖ / (1 - ‖q‖) ≤ (1 / 24 : ℝ) := by
    apply (div_le_iff₀ (sub_pos.mpr hq1)).mpr
    linarith
  have hAe : ‖A - 1‖ ≤ (1 / 24 : ℝ) :=
    (norm_sum_complexSeries_thetaThreeSeries_sub_one_le hq1).trans hsmall
  have hBe : ‖B - 1‖ ≤ (1 / 24 : ℝ) :=
    (norm_sum_complexSeries_thetaFourSeries_sub_one_le hq1).trans hsmall
  have hAlow : (23 / 24 : ℝ) ≤ ‖A‖ := by
    have h := norm_sub_norm_le (1 : ℂ) A
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hAup : ‖A‖ ≤ (25 / 24 : ℝ) := by
    have h := norm_add_le (A - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hBup : ‖B‖ ≤ (25 / 24 : ℝ) := by
    have h := norm_add_le (B - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hAB : ‖A - B‖ ≤ (1 / 12 : ℝ) := by
    have h := norm_sub_le (A - 1) (B - 1)
    rw [show A - 1 - (B - 1) = A - B by ring] at h
    linarith
  have hAdd : ‖A + B‖ ≤ (25 / 12 : ℝ) := by
    linarith [norm_add_le A B]
  have hSq : ‖A ^ 2 + B ^ 2‖ ≤ (625 / 288 : ℝ) := by
    have h := norm_add_le (A ^ 2) (B ^ 2)
    rw [norm_pow, norm_pow] at h
    nlinarith [norm_nonneg A, norm_nonneg B]
  have hnum : ‖A ^ 4 - B ^ 4‖ ≤ (1 / 12 : ℝ) * (25 / 12) * (625 / 288) := by
    rw [show A ^ 4 - B ^ 4 = (A - B) * (A + B) * (A ^ 2 + B ^ 2) by ring,
      norm_mul, norm_mul]
    exact mul_le_mul
      (mul_le_mul hAB hAdd (norm_nonneg _) (by norm_num)) hSq
      (norm_nonneg _) (by norm_num)
  have hden : (23 / 24 : ℝ) ^ 4 ≤ ‖A‖ ^ 4 := by gcongr
  have hA0 : A ≠ 0 := sum_complexSeries_thetaThreeSeries_ne_zero hq1
  have hexpr : levelTwoLambda q = (A ^ 4 - B ^ 4) / A ^ 4 := by
    change 1 - B ^ 4 / A ^ 4 = _
    field_simp [hA0]
  calc
    ‖levelTwoLambda q‖ = ‖A ^ 4 - B ^ 4‖ / ‖A‖ ^ 4 := by
      rw [hexpr, norm_div, norm_pow]
    _ ≤ ((1 / 12 : ℝ) * (25 / 12) * (625 / 288)) / ‖A‖ ^ 4 :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((1 / 12 : ℝ) * (25 / 12) * (625 / 288)) / (23 / 24) ^ 4 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
    _ < 1 / 2 := by norm_num

end DirichletL
