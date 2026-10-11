import Analysis.ContourCayley

/-!
Cayley differences for the slit maps in CDT v2, supplied TeX 10003-10019.
-/

namespace DirichletL

theorem cayleyMap_sub {z w : ℂ} (hz : z ≠ 1) (hw : w ≠ 1) :
    cayleyMap z - cayleyMap w = 2 * (z - w) / ((1 - z) * (1 - w)) := by
  dsimp only [cayleyMap]
  field_simp [sub_ne_zero.mpr hz.symm, sub_ne_zero.mpr hw.symm]
  ring

theorem inverseCayleyMap_sub {z w : ℂ} (hz : z + 1 ≠ 0) (hw : w + 1 ≠ 0) :
    inverseCayleyMap z - inverseCayleyMap w =
      2 * (z - w) / ((z + 1) * (w + 1)) := by
  dsimp only [inverseCayleyMap]
  field_simp [hz, hw]
  ring

theorem norm_cayleyMap_sub_le {z w : ℂ} {δ β : ℝ}
    (hδ : ‖z - w‖ ≤ δ) (hβ : β ≤ ‖1 - w‖) (hδβ : δ < β) :
    ‖cayleyMap z - cayleyMap w‖ ≤ 2 * δ / (β * (β - δ)) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hβ0 : 0 < β := hδ0.trans_lt hδβ
  have htri := norm_add_le (1 - z) (z - w)
  rw [show (1 - z) + (z - w) = 1 - w by ring] at htri
  have hlow : β - δ ≤ ‖1 - z‖ := by linarith only [htri, hδ, hβ]
  have hz0 : 1 - z ≠ 0 := norm_pos_iff.mp ((sub_pos.mpr hδβ).trans_le hlow)
  have hw0 : 1 - w ≠ 0 := norm_pos_iff.mp (hβ0.trans_le hβ)
  have hz1 : z ≠ 1 := (sub_ne_zero.mp hz0).symm
  have hw1 : w ≠ 1 := (sub_ne_zero.mp hw0).symm
  have hden : β * (β - δ) ≤ ‖1 - z‖ * ‖1 - w‖ := by
    rw [mul_comm β]
    exact mul_le_mul hlow hβ hβ0.le (norm_nonneg _)
  calc
    _ = 2 * ‖z - w‖ / (‖1 - z‖ * ‖1 - w‖) := by
      rw [cayleyMap_sub hz1 hw1, norm_div, norm_mul, norm_mul]
      norm_num
    _ ≤ 2 * δ / (‖1 - z‖ * ‖1 - w‖) :=
      div_le_div_of_nonneg_right (by linarith only [hδ]) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
      (mul_pos hβ0 (sub_pos.mpr hδβ)) hden

theorem norm_inverseCayleyMap_sub_le {z w : ℂ} {δ β : ℝ}
    (hδ : ‖z - w‖ ≤ δ) (hβ : β ≤ ‖w + 1‖) (hδβ : δ < β) :
    ‖inverseCayleyMap z - inverseCayleyMap w‖ ≤ 2 * δ / (β * (β - δ)) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hβ0 : 0 < β := hδ0.trans_lt hδβ
  have htri := norm_sub_le (z + 1) (z - w)
  rw [show (z + 1) - (z - w) = w + 1 by ring] at htri
  have hlow : β - δ ≤ ‖z + 1‖ := by linarith only [htri, hδ, hβ]
  have hz0 : z + 1 ≠ 0 := norm_pos_iff.mp ((sub_pos.mpr hδβ).trans_le hlow)
  have hw0 : w + 1 ≠ 0 := norm_pos_iff.mp (hβ0.trans_le hβ)
  have hden : β * (β - δ) ≤ ‖z + 1‖ * ‖w + 1‖ := by
    rw [mul_comm β]
    exact mul_le_mul hlow hβ hβ0.le (norm_nonneg _)
  calc
    _ = 2 * ‖z - w‖ / (‖z + 1‖ * ‖w + 1‖) := by
      rw [inverseCayleyMap_sub hz0 hw0, norm_div, norm_mul, norm_mul]
      norm_num
    _ ≤ 2 * δ / (‖z + 1‖ * ‖w + 1‖) :=
      div_le_div_of_nonneg_right (by linarith only [hδ]) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
      (mul_pos hβ0 (sub_pos.mpr hδβ)) hden

end DirichletL
