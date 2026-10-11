import Analysis.ContourReverseMap
import Analysis.ContourSlitLocalInverse
import Analysis.ContourLuneLocalInverse

/-!
A small disc in the image of the corrected CDT contour, author Appendix A.4,
pages 204-205. Meanings and component bounds precede these bodies in
-/

namespace DirichletL

theorem cdtContourReverseMap_spec {q : ℂ} (hq : ‖q‖ ≤ 1 / 10000) :
    ‖cdtContourReverseMap q‖ ≤ 5184 * ‖q‖ ∧
      cdtContourDiskMap ((1000 / 995 : ℂ) * cdtContourReverseMap q) = q := by
  let u : ℂ := -(100 / 77 : ℂ) * q
  let v4 : ℂ := -(contourRotation (-783 / 10000))⁻¹ * luneMap ((75 / 10 : ℝ) : ℂ) u
  let v3 : ℂ := (contourRotation (3525 / 100000))⁻¹ * contourSlitInverse (772 / 1000) v4
  let v2 : ℂ := (contourRotation (11543 / 100000))⁻¹ * contourSlitInverse (55515 / 100000) v3
  let v1 : ℂ := (contourRotation (7977 / 100000))⁻¹ * contourSlitInverse (6188 / 10000) v2
  let v0 : ℂ := contourSlitInverse (91 / 100) v1
  have hunit (theta : ℝ) : contourRotation theta ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_contourRotation]
    norm_num
  have hu : ‖u‖ ≤ 2 * ‖q‖ := by
    dsimp only [u]
    rw [norm_mul, norm_neg]
    norm_num
    nlinarith only [norm_nonneg q]
  have hu1 : ‖u‖ ≤ 1 / 10 := by linarith only [hu, hq]
  have hL : ‖luneMap ((75 / 10 : ℝ) : ℂ) u‖ ≤ 2 * ‖u‖ :=
    norm_luneMap_ofReal_le_two_mul (by norm_num) (by norm_num) hu1
  have h4 : ‖v4‖ ≤ 4 * ‖q‖ := by
    dsimp only [v4]
    rw [norm_mul, norm_neg, norm_inv, norm_contourRotation, inv_one, one_mul]
    linarith only [hL, hu]
  have h4small : ‖v4‖ ≤ 1 / 10 := by linarith only [h4, hq]
  have h3 : ‖v3‖ ≤ 24 * ‖q‖ := by
    have h := norm_contourSlitInverse_le_six_mul (r := 772 / 1000) (by norm_num) h4small
    dsimp only [v3]
    rw [norm_mul, norm_inv, norm_contourRotation, inv_one, one_mul]
    linarith only [h, h4]
  have h3small : ‖v3‖ ≤ 1 / 10 := by linarith only [h3, hq]
  have h2 : ‖v2‖ ≤ 144 * ‖q‖ := by
    have h := norm_contourSlitInverse_le_six_mul (r := 55515 / 100000) (by norm_num) h3small
    dsimp only [v2]
    rw [norm_mul, norm_inv, norm_contourRotation, inv_one, one_mul]
    linarith only [h, h3]
  have h2small : ‖v2‖ ≤ 1 / 10 := by linarith only [h2, hq]
  have h1 : ‖v1‖ ≤ 864 * ‖q‖ := by
    have h := norm_contourSlitInverse_le_six_mul (r := 6188 / 10000) (by norm_num) h2small
    dsimp only [v1]
    rw [norm_mul, norm_inv, norm_contourRotation, inv_one, one_mul]
    linarith only [h, h2]
  have h1small : ‖v1‖ ≤ 1 / 10 := by linarith only [h1, hq]
  have h0 : ‖v0‖ ≤ 5184 * ‖q‖ := by
    have h := norm_contourSlitInverse_le_six_mul (r := 91 / 100) (by norm_num) h1small
    change ‖contourSlitInverse (91 / 100) v1‖ ≤ _
    linarith only [h, h1]
  have hundo1 : contourSlitMap (91 / 100) v0 = v1 :=
    contourSlitMap_contourSlitInverse (by norm_num) (by norm_num)
      (h1small.trans_lt (by norm_num))
  have hundo2 : contourSlitMap (6188 / 10000) (contourRotation (7977 / 100000) * v1) = v2 := by
    dsimp only [v1]
    rw [mul_inv_cancel_left₀ (hunit _)]
    exact contourSlitMap_contourSlitInverse (by norm_num) (by norm_num)
      (h2small.trans_lt (by norm_num))
  have hundo3 : contourSlitMap (55515 / 100000) (contourRotation (11543 / 100000) * v2) = v3 := by
    dsimp only [v2]
    rw [mul_inv_cancel_left₀ (hunit _)]
    exact contourSlitMap_contourSlitInverse (by norm_num) (by norm_num)
      (h3small.trans_lt (by norm_num))
  have hundo4 : contourSlitMap (772 / 1000) (contourRotation (3525 / 100000) * v3) = v4 := by
    dsimp only [v3]
    rw [mul_inv_cancel_left₀ (hunit _)]
    exact contourSlitMap_contourSlitInverse (by norm_num) (by norm_num)
      (h4small.trans_lt (by norm_num))
  have houter : -contourRotation (-783 / 10000) * v4 = luneMap ((75 / 10 : ℝ) : ℂ) u := by
    dsimp only [v4]
    calc
      _ = contourRotation (-783 / 10000) *
          ((contourRotation (-783 / 10000))⁻¹ * luneMap ((75 / 10 : ℝ) : ℂ) u) := by ring
      _ = _ := mul_inv_cancel_left₀ (hunit _) _
  have hLu : contourLuneMap (75 / 10) (luneMap ((75 / 10 : ℝ) : ℂ) u) = u := by
    apply contourLuneMap_luneMap (by norm_num)
    · norm_num
      linarith only [hu1]
    · linarith only [hL, hu, hq]
  refine ⟨h0, ?_⟩
  change cdtContourDiskMap ((1000 / 995 : ℂ) * v0) = q
  dsimp only [cdtContourDiskMap]
  rw [show (995 / 1000 : ℂ) * ((1000 / 995 : ℂ) * v0) = v0 by ring,
    hundo1, hundo2, hundo3, hundo4, houter, hLu]
  dsimp only [u]
  ring

theorem mem_image_cdtContourDiskMap_of_norm_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 10000) :
    q ∈ cdtContourDiskMap '' Metric.ball (0 : ℂ) 1 := by
  have h := cdtContourReverseMap_spec hq
  refine ⟨(1000 / 995 : ℂ) * cdtContourReverseMap q, ?_, h.2⟩
  simp only [Metric.mem_ball, dist_zero_right, norm_mul]
  norm_num
  nlinarith only [h.1, hq]

end DirichletL
