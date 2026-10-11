import Analysis.ContourLune

/-!
Product variation for the CDT lune inverse, supplied TeX 9956-9964.
Meanings and positive-factor checks precede these bodies in
-/

namespace DirichletL

theorem norm_contourLuneMap_sub_le {c : ℝ} (hc : 1 < c) {z w : ℂ} {δ κ : ℝ}
    (hδ : ‖z - w‖ ≤ δ)
    (hκ : ‖contourHalfPlaneRoot (((c ^ 2 - 1) / (c ^ 2 + 1)) ^ 2) (cayleyMap z) -
      contourHalfPlaneRoot (((c ^ 2 - 1) / (c ^ 2 + 1)) ^ 2) (cayleyMap w)‖ ≤ κ) :
    ‖contourLuneMap c z - contourLuneMap c w‖ ≤
      ((‖1 - w‖ + δ) * κ + δ *
        ‖contourHalfPlaneRoot (((c ^ 2 - 1) / (c ^ 2 + 1)) ^ 2) (cayleyMap w) - 1‖) /
      (2 * ((c ^ 2 - 1) / (c ^ 2 + 1))) := by
  let a : ℝ := (c ^ 2 - 1) / (c ^ 2 + 1)
  let K (v : ℂ) : ℂ := contourHalfPlaneRoot (a ^ 2) (cayleyMap v)
  have ha : 0 < a := (lune_factor_mem_Ioo hc).1
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  change ‖K z - K w‖ ≤ κ at hκ
  change ‖contourLuneMap c z - contourLuneMap c w‖ ≤
    ((‖1 - w‖ + δ) * κ + δ * ‖K w - 1‖) / (2 * a)
  have hz : ‖1 - z‖ ≤ ‖1 - w‖ + δ := by
    have h := norm_sub_le (1 - w) (z - w)
    rw [show (1 - w) - (z - w) = 1 - z by ring] at h
    exact h.trans (add_le_add_left hδ _)
  have heq : contourLuneMap c z - contourLuneMap c w =
      ((1 - z) * (K z - K w) - (z - w) * (K w - 1)) / (2 * (a : ℂ)) := by
    simp only [contourLuneMap, K, a, div_eq_mul_inv]
    ring
  have hden : ‖2 * (a : ℂ)‖ = 2 * a := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    norm_num
  rw [heq, norm_div, hden]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ‖(1 - z) * (K z - K w)‖ + ‖(z - w) * (K w - 1)‖ := norm_sub_le _ _
    _ = ‖1 - z‖ * ‖K z - K w‖ + ‖z - w‖ * ‖K w - 1‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ _ := add_le_add (mul_le_mul hz hκ (norm_nonneg _) (by positivity))
      (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))

end DirichletL
