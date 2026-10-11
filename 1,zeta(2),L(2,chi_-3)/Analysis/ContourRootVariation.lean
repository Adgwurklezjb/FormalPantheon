import Analysis.ContourHalfPlaneRoot

/-!
Root differences for CDT v2's slit components, supplied TeX 10003-10019.
Meanings and lower-bound guards precede these bodies in
-/

namespace DirichletL

theorem norm_sq_sub_sq_le_of_norm_sub_le {z w : ℂ} {δ : ℝ}
    (hδ : ‖z - w‖ ≤ δ) :
    ‖z ^ 2 - w ^ 2‖ ≤ δ * (2 * ‖w‖ + δ) := by
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hz : ‖z‖ ≤ ‖w‖ + δ := by
    have h := norm_add_le (z - w) w
    rw [sub_add_cancel] at h
    linarith only [h, hδ]
  have hs : ‖z + w‖ ≤ 2 * ‖w‖ + δ := by
    have h := norm_add_le z w
    linarith only [h, hz]
  rw [show z ^ 2 - w ^ 2 = (z - w) * (z + w) by ring, norm_mul]
  exact mul_le_mul hδ hs (norm_nonneg _) hδ0

theorem norm_cpow_inv_two_sub_le {z w : ℂ} {δ β : ℝ}
    (hδ : ‖z - w‖ ≤ δ)
    (hβ : β ≤ ‖z ^ (2⁻¹ : ℂ) + w ^ (2⁻¹ : ℂ)‖) (hβ0 : 0 < β) :
    ‖z ^ (2⁻¹ : ℂ) - w ^ (2⁻¹ : ℂ)‖ ≤ δ / β := by
  have heq : (z ^ (2⁻¹ : ℂ) - w ^ (2⁻¹ : ℂ)) *
      (z ^ (2⁻¹ : ℂ) + w ^ (2⁻¹ : ℂ)) = z - w := by
    calc
      _ = (z ^ (2⁻¹ : ℂ)) ^ 2 - (w ^ (2⁻¹ : ℂ)) ^ 2 := by ring
      _ = _ := by rw [Complex.cpow_ofNat_inv_pow _ 2, Complex.cpow_ofNat_inv_pow _ 2]
  apply (le_div_iff₀ hβ0).mpr
  calc
    _ ≤ ‖z ^ (2⁻¹ : ℂ) - w ^ (2⁻¹ : ℂ)‖ *
        ‖z ^ (2⁻¹ : ℂ) + w ^ (2⁻¹ : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hβ (norm_nonneg _)
    _ = ‖z - w‖ := by rw [← norm_mul, heq]
    _ ≤ δ := hδ

theorem norm_contourHalfPlaneRoot_sub_le {d : ℝ} {z w : ℂ} {δ β : ℝ}
    (hδ : ‖z - w‖ ≤ δ)
    (hβ : β ≤ ‖contourHalfPlaneRoot d z + contourHalfPlaneRoot d w‖)
    (hβ0 : 0 < β) :
    ‖contourHalfPlaneRoot d z - contourHalfPlaneRoot d w‖ ≤
      |d| * δ * (2 * ‖w‖ + δ) / β := by
  have harg : ‖((1 - (d : ℂ)) + (d : ℂ) * z ^ 2) -
      ((1 - (d : ℂ)) + (d : ℂ) * w ^ 2)‖ ≤ |d| * δ * (2 * ‖w‖ + δ) := by
    rw [show ((1 - (d : ℂ)) + (d : ℂ) * z ^ 2) -
      ((1 - (d : ℂ)) + (d : ℂ) * w ^ 2) = (d : ℂ) * (z ^ 2 - w ^ 2) by ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |d| * (δ * (2 * ‖w‖ + δ)) :=
        mul_le_mul_of_nonneg_left (norm_sq_sub_sq_le_of_norm_sub_le hδ) (abs_nonneg d)
      _ = _ := by ring
  exact norm_cpow_inv_two_sub_le harg hβ hβ0

end DirichletL
