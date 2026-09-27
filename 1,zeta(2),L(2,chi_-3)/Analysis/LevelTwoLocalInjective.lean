import Analysis.LevelTwoLogTail
import Analysis.LevelTwoRealPreimage
import Analysis.Contours

/-!
Local uniqueness of the central root in CDT author Lemma A.4.4, page 205,
using the level-two product recalled on page 204 and exact Cauchy bounds.
Meanings and closed-disc checks precede these bodies in
-/

namespace DirichletL

theorem norm_levelTwoHauptmodul_add_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 100) :
    ‖levelTwoHauptmodul q + 256 * q‖ ≤ 2 := by
  have hlog : ‖levelTwoLogSeries q‖ ≤ 1 / 66 := by
    have h := norm_levelTwoLogSeries_sub_sum_le 0 hq (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hmul : ‖24 * levelTwoLogSeries q‖ ≤ 4 / 11 := by
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  have hexpbound : ‖Complex.exp (24 * levelTwoLogSeries q) - 1‖ ≤ 8 / 11 := by
    have h := Complex.norm_exp_sub_one_le (hmul.trans (by norm_num))
    linarith
  have hexp : Complex.exp (24 * levelTwoLogSeries q) =
      (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 24 := by
    simpa only [Nat.cast_ofNat,
      exp_levelTwoLogSeries_eq_product (hq.trans_lt (by norm_num))] using
      Complex.exp_nat_mul (levelTwoLogSeries q) 24
  have heq : levelTwoHauptmodul q + 256 * q =
      -256 * q * (Complex.exp (24 * levelTwoLogSeries q) - 1) := by
    rw [hexp]
    unfold levelTwoHauptmodul
    ring
  rw [heq, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
  calc
    _ ≤ (256 * (1 / 100)) * (8 / 11) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num)) hexpbound
        (norm_nonneg _) (by norm_num)
    _ ≤ 2 := by norm_num

theorem norm_deriv_levelTwoHauptmodul_add_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 1000) :
    ‖deriv (fun w : ℂ => levelTwoHauptmodul w + 256 * w) q‖ ≤ 224 := by
  let E (w : ℂ) : ℂ := levelTwoHauptmodul w + 256 * w
  have hsmall : ∀ w ∈ Metric.closedBall q (9 / 1000), ‖w‖ ≤ 1 / 100 := by
    intro w hw
    have hwq : ‖w - q‖ ≤ 9 / 1000 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    calc
      ‖w‖ = ‖(w - q) + q‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - q‖ + ‖q‖ := norm_add_le _ _
      _ ≤ 9 / 1000 + 1 / 1000 := add_le_add hwq hq
      _ = 1 / 100 := by norm_num
  have hd : DifferentiableOn ℂ E (Metric.closedBall q (9 / 1000)) := by
    intro w hw
    have hw1 : w ∈ Metric.ball (0 : ℂ) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        (hsmall w hw).trans_lt (by norm_num : (1 / 100 : ℝ) < 1)
    have hlin : DifferentiableAt ℂ (fun v : ℂ => 256 * v) w := by fun_prop
    exact ((analyticOnNhd_levelTwoHauptmodul w hw1).differentiableAt.add
      hlin).differentiableWithinAt
  have hbound := contour_derivative_bound (c := q) (R := 9 / 1000) (C := 2)
    (f := E) (by norm_num)
    (hd.mono Metric.closure_ball_subset_closedBall).diffContOnCl
    (fun w hw => norm_levelTwoHauptmodul_add_le
      (hsmall w (Metric.sphere_subset_closedBall hw)))
  exact hbound.trans (by norm_num)

theorem injOn_levelTwoHauptmodul_smallBall :
    Set.InjOn levelTwoHauptmodul (Metric.closedBall (0 : ℂ) (1 / 1000)) := by
  let E (w : ℂ) : ℂ := levelTwoHauptmodul w + 256 * w
  have hd : ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 1000), DifferentiableAt ℂ E w := by
    intro w hw
    have hw0 : ‖w‖ ≤ 1 / 1000 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hw
    have hw1 : w ∈ Metric.ball (0 : ℂ) 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        hw0.trans_lt (by norm_num : (1 / 1000 : ℝ) < 1)
    have hlin : DifferentiableAt ℂ (fun v : ℂ => 256 * v) w := by fun_prop
    exact (analyticOnNhd_levelTwoHauptmodul w hw1).differentiableAt.add hlin
  intro z hz w hw heq
  have hbound := (convex_closedBall (0 : ℂ) (1 / 1000)).norm_image_sub_le_of_norm_deriv_le
    hd (fun v hv => norm_deriv_levelTwoHauptmodul_add_le
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)) hz hw
  have hsub : E w - E z = 256 * (w - z) := by
    dsimp only [E]
    rw [heq]
    ring
  rw [hsub, norm_mul, Complex.norm_ofNat] at hbound
  have hzero : ‖w - z‖ = 0 := by nlinarith [norm_nonneg (w - z)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

theorem existsUnique_levelTwoHauptmodul_eq_neg_one_div_seventyTwo_smallBall :
    ∃! q : ℂ, ‖q‖ ≤ 1 / 1000 ∧ levelTwoHauptmodul q = -1 / 72 := by
  obtain ⟨q, hq, hvalue⟩ := exists_levelTwoHauptmodul_eq_neg_one_div_seventyTwo
  have hqnorm : ‖(q : ℂ)‖ ≤ 1 / 1000 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq.1]
    exact hq.2.le.trans (by norm_num)
  refine ⟨(q : ℂ), ⟨hqnorm, hvalue⟩, ?_⟩
  intro w hw
  apply injOn_levelTwoHauptmodul_smallBall
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw.1)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hqnorm)
  exact hw.2.trans hvalue.symm

end DirichletL
