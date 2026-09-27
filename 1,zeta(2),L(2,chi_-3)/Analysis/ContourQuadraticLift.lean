import Analysis.ContourNomeSquareRoot
import Analysis.LevelTwoLambdaBounds
import Analysis.ContourCentralBounds

/-!
The concrete original-coordinate lift of the contour on the double disc.
Source: CDT v2 TeX 7157-7173 and 7176-7197; author Appendix A.4, pages 204-205.
-/

namespace DirichletL

theorem exists_analytic_cdtContour_original_coordinate :
    ∃ X : ℂ → ℂ, AnalyticOnNhd ℂ X (Metric.ball 0 1) ∧ X 0 = 0 ∧
      (∀ z : ℂ, ‖z‖ < 1 → X z ≠ 1) ∧
      (∀ z : ℂ, ‖z‖ < 1 → (X z = 0 ↔ z = 0)) ∧
      (∀ z : ℂ, ‖z‖ < 1 → mobiusCoordinate (X z) = cdtContourMap (z ^ 2)) ∧
      (∀ z : ℂ, ‖z‖ < 1 → X (-z) = mobiusAnalyticInvolution (X z)) ∧
      ∀ z : ℂ, ‖z‖ < 1 / 50 → ‖X z‖ < 1 / 2 := by
  obtain ⟨t, hta, ht0, htneg, htsq⟩ := exists_analytic_cdtContourNome_square_root
  have hsq (z : ℂ) (hz : ‖z‖ < 1) : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z]
  have htunit (z : ℂ) (hz : ‖z‖ < 1) : ‖t z‖ < 1 := by
    have he : ‖t z‖ ^ 2 = ‖cdtContourDiskMap (z ^ 2)‖ := by
      simpa only [norm_pow] using congrArg norm (htsq z hz)
    have hb := norm_cdtContourDiskMap_lt (hsq z hz).le
    nlinarith [norm_nonneg (t z)]
  have htbound (z : ℂ) (hz : ‖z‖ < 1) : ‖t z‖ ≤ ‖z‖ := by
    have he : ‖t z‖ ^ 2 = ‖cdtContourDiskMap (z ^ 2)‖ := by
      simpa only [norm_pow] using congrArg norm (htsq z hz)
    have hb := norm_cdtContourDiskMap_le_mul (hsq z hz)
    rw [norm_pow] at hb
    nlinarith [norm_nonneg (t z), norm_nonneg z]
  let X (z : ℂ) := levelTwoLambda (t z)
  have hX0 : X 0 = 0 := by simp [X, ht0, levelTwoLambda_zero]
  have hY (z : ℂ) (hz : ‖z‖ < 1) :
      mobiusCoordinate (X z) = cdtContourMap (z ^ 2) := by
    dsimp only [X]
    rw [mobiusCoordinate_levelTwoLambda (htunit z hz), htsq z hz]
    rfl
  refine ⟨X, ?_, hX0, fun z hz => levelTwoLambda_ne_one (htunit z hz),
    ?_, hY, ?_, ?_⟩
  · intro z hz
    have htz : t z ∈ Metric.ball (0 : ℂ) 1 := by
      simpa using htunit z (by simpa using hz)
    exact (analyticOnNhd_levelTwoLambda _ htz).comp' (hta z hz)
  · intro z hz
    constructor
    · intro he
      have h := hY z hz
      rw [he] at h
      have hzsq : z ^ 2 = 0 :=
        (cdtContourMap_eq_zero_iff (hsq z hz).le).mp (by simpa [mobiusCoordinate] using h.symm)
      exact sq_eq_zero_iff.mp hzsq
    · rintro rfl
      exact hX0
  · intro z hz
    dsimp only [X]
    rw [htneg, levelTwoLambda_neg (htunit z hz)]
  · intro z hz
    exact norm_levelTwoLambda_lt_half
      ((htbound z (hz.trans (by norm_num))).trans_lt hz)

theorem norm_lt_one_div_sixty_of_cdtContourMap_sq_eq {z : ℂ}
    (hz : ‖z‖ ≤ 1) (hv : cdtContourMap (z ^ 2) = -1 / 72) :
    ‖z‖ < 1 / 60 := by
  have hzsq : z ^ 2 ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_pow]
    nlinarith [norm_nonneg z]
  have h := norm_lt_one_div_fiveThousand_of_cdtContourMap_eq hzsq hv
  rw [norm_pow] at h
  nlinarith [norm_nonneg z]

end DirichletL
