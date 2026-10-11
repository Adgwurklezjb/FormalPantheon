import Analysis.ContourDiskMap
import Analysis.ContourSlitInverse

/-!
A necessary image condition for CDT's corrected contour, author Appendix A.4, page 204.
-/

namespace DirichletL

/-- The total reverse expression for the corrected slit/lune contour, before undoing its shrink. -/
noncomputable def cdtContourReverseMap (q : ℂ) : ℂ :=
  let v4 := -(contourRotation (-783 / 10000))⁻¹ *
    luneMap ((75 / 10 : ℝ) : ℂ) (-(100 / 77 : ℂ) * q)
  let v3 := (contourRotation (3525 / 100000))⁻¹ * contourSlitInverse (772 / 1000) v4
  let v2 := (contourRotation (11543 / 100000))⁻¹ * contourSlitInverse (55515 / 100000) v3
  let v1 := (contourRotation (7977 / 100000))⁻¹ * contourSlitInverse (6188 / 10000) v2
  contourSlitInverse (91 / 100) v1

theorem cdtContourReverseMap_cdtContourDiskMap {z : ℂ} (hz : ‖z‖ ≤ 1) :
    cdtContourReverseMap (cdtContourDiskMap z) = (995 / 1000 : ℂ) * z := by
  let z0 : ℂ := (995 / 1000 : ℂ) * z
  let z1 : ℂ := contourSlitMap (91 / 100) z0
  let z2 : ℂ := contourSlitMap (6188 / 10000) (contourRotation (7977 / 100000) * z1)
  let z3 : ℂ := contourSlitMap (55515 / 100000) (contourRotation (11543 / 100000) * z2)
  let z4 : ℂ := contourSlitMap (772 / 1000) (contourRotation (3525 / 100000) * z3)
  have hunit (theta : ℝ) : contourRotation theta ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_contourRotation]
    norm_num
  have h0 : ‖z0‖ < 1 := by
    dsimp only [z0]
    rw [norm_mul]
    norm_num
    nlinarith only [hz]
  have h1 : ‖z1‖ < 1 :=
    norm_contourSlitMap_lt_one (r := 91 / 100) (by norm_num) (by norm_num) h0
  have h1r : ‖contourRotation (7977 / 100000) * z1‖ < 1 := by
    simpa only [norm_mul, norm_contourRotation, one_mul] using h1
  have h2 : ‖z2‖ < 1 :=
    norm_contourSlitMap_lt_one (r := 6188 / 10000) (by norm_num) (by norm_num) h1r
  have h2r : ‖contourRotation (11543 / 100000) * z2‖ < 1 := by
    simpa only [norm_mul, norm_contourRotation, one_mul] using h2
  have h3 : ‖z3‖ < 1 :=
    norm_contourSlitMap_lt_one (r := 55515 / 100000) (by norm_num) (by norm_num) h2r
  have h3r : ‖contourRotation (3525 / 100000) * z3‖ < 1 := by
    simpa only [norm_mul, norm_contourRotation, one_mul] using h3
  have h4 : ‖z4‖ < 1 :=
    norm_contourSlitMap_lt_one (r := 772 / 1000) (by norm_num) (by norm_num) h3r
  have h4r : ‖-contourRotation (-783 / 10000) * z4‖ < 1 := by
    simpa only [norm_mul, norm_neg, norm_contourRotation, one_mul] using h4
  have he1 : contourSlitInverse (91 / 100) z1 = z0 :=
    contourSlitInverse_contourSlitMap (r := 91 / 100) (by norm_num) (by norm_num) h0
  have he2 : contourSlitInverse (6188 / 10000) z2 = contourRotation (7977 / 100000) * z1 :=
    contourSlitInverse_contourSlitMap (r := 6188 / 10000) (by norm_num) (by norm_num) h1r
  have he3 : contourSlitInverse (55515 / 100000) z3 = contourRotation (11543 / 100000) * z2 :=
    contourSlitInverse_contourSlitMap (r := 55515 / 100000) (by norm_num) (by norm_num) h2r
  have he4 : contourSlitInverse (772 / 1000) z4 = contourRotation (3525 / 100000) * z3 :=
    contourSlitInverse_contourSlitMap (r := 772 / 1000) (by norm_num) (by norm_num) h3r
  have houter : -(100 / 77 : ℂ) * cdtContourDiskMap z =
      contourLuneMap (75 / 10) (-contourRotation (-783 / 10000) * z4) := by
    change -(100 / 77 : ℂ) * (-(77 / 100 : ℂ) *
      contourLuneMap (75 / 10) (-contourRotation (-783 / 10000) * z4)) = _
    ring
  have hrev4 : -(contourRotation (-783 / 10000))⁻¹ *
      luneMap ((75 / 10 : ℝ) : ℂ) (-(100 / 77 : ℂ) * cdtContourDiskMap z) = z4 := by
    rw [houter, luneMap_contourLuneMap (c := 75 / 10) (by norm_num) h4r]
    calc
      _ = (contourRotation (-783 / 10000))⁻¹ *
          (contourRotation (-783 / 10000) * z4) := by ring
      _ = z4 := inv_mul_cancel_left₀ (hunit _) _
  dsimp only [cdtContourReverseMap]
  rw [hrev4, he4, inv_mul_cancel_left₀ (hunit (3525 / 100000)),
    he3, inv_mul_cancel_left₀ (hunit (11543 / 100000)),
    he2, inv_mul_cancel_left₀ (hunit (7977 / 100000)), he1]

theorem norm_cdtContourReverseMap_le {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖cdtContourReverseMap (cdtContourDiskMap z)‖ ≤ (995 / 1000 : ℝ) := by
  rw [cdtContourReverseMap_cdtContourDiskMap hz, norm_mul]
  norm_num
  nlinarith only [hz]

theorem not_mem_image_cdtContourDiskMap_of_reverse_norm {q : ℂ}
    (hq : (995 / 1000 : ℝ) < ‖cdtContourReverseMap q‖) :
    q ∉ cdtContourDiskMap '' Metric.closedBall (0 : ℂ) 1 := by
  rintro ⟨z, hz, rfl⟩
  have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  exact (not_lt_of_ge (norm_cdtContourReverseMap_le hz1)) hq

end DirichletL
