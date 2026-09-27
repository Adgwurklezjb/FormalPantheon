import Analysis.Contours

/-!
Exact scalar slack for CDT v2's two-radius application, TeX 8384-8404
and 10096-10108. Meanings precede these bodies in
-/

namespace DirichletL

theorem log_two_gt_6931_div_10000 : (6931 / 10000 : ℝ) < Real.log 2 := by
  have hs := Real.hasSum_log_one_add (show (0 : ℝ) ≤ 1 by norm_num)
  have hp := sum_le_hasSum (Finset.range 4) (by intro k _; positivity) hs
  norm_num [Finset.sum_range_succ] at hp
  linarith only [hp]

theorem log_cdtContour_derivative_gt :
    (127 / 25 : ℝ) < Real.log (256 * cdtContourConformalRadius) := by
  have hratio := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 33 / 128 by norm_num)
  norm_num at hratio
  have hsplit : Real.log (161 : ℝ) = 7 * Real.log 2 + Real.log (161 / 128 : ℝ) := by
    calc
      _ = Real.log ((2 : ℝ) ^ 7 * (161 / 128)) := congrArg Real.log (by norm_num)
      _ = _ := by
        rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
        norm_num
  have h161 : (127 / 25 : ℝ) < Real.log 161 := by
    rw [hsplit]
    linarith only [log_two_gt_6931_div_10000, hratio]
  have hscale : (161 : ℝ) < 256 * cdtContourConformalRadius := by
    rw [cdtContourConformalRadius_eq]
    norm_num
  exact h161.trans (Real.log_lt_log (by norm_num) hscale)

theorem cdt_two_radius_margin :
    (57 / 5 : ℝ) + 824631 / 7000000 <
      14 * (Real.log (256 * cdtContourConformalRadius) -
        16603 / 3920 - (209 / 1000 : ℝ) ^ 2 / 2) := by
  have h := log_cdtContour_derivative_gt
  norm_num at h ⊢
  linarith only [h]

end DirichletL
