import Analysis.LevelTwoLogTail
import Analysis.LevelTwoLocalInjective

/-!
A refined positive-root interval for CDT author Lemma A.4.4, page 205.
Meanings, finite-product error, and endpoint signs precede the bodies in
-/

namespace DirichletL

private theorem norm_levelTwoHauptmodul_sub_four_le {q : ℂ}
    (hq : ‖q‖ ≤ 1 / 10000) :
    ‖levelTwoHauptmodul q -
      (-256 * q * (∏ n ∈ Finset.range 4, (1 + q ^ (n + 1))) ^ 24)‖ ≤
      (256 * ‖q‖ * ‖∏ n ∈ Finset.range 4, (1 + q ^ (n + 1))‖ ^ 24) /
        1000000000000000000 := by
  let S : ℂ := ∑ n ∈ Finset.range 4, Complex.log (1 + q ^ (n + 1))
  let P : ℂ := ∏ n ∈ Finset.range 4, (1 + q ^ (n + 1))
  let z : ℂ := 24 * (levelTwoLogSeries q - S)
  have hq1 : ‖q‖ < 1 := hq.trans_lt (by norm_num)
  have hz : ‖z‖ ≤ 1 / 2000000000000000000 := by
    have ht := norm_levelTwoLogSeries_sub_sum_le 4 hq (by norm_num) (by norm_num)
    norm_num at ht
    dsimp only [z, S]
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  have herr : ‖Complex.exp z - 1‖ ≤ 1 / 1000000000000000000 := by
    have h := Complex.norm_exp_sub_one_le (hz.trans (by norm_num))
    linarith
  have hfinite : Complex.exp S = P := by
    dsimp only [S, P]
    rw [Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro n hn
    apply Complex.exp_log
    apply Complex.slitPlane_ne_zero
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_pow]
    calc
      ‖q‖ ^ (n + 1) ≤ ‖q‖ := by
        simpa only [pow_one] using pow_le_pow_of_le_one (norm_nonneg q) hq1.le
          (show 1 ≤ n + 1 by omega)
      _ < 1 := hq1
  have hinf : Complex.exp (24 * levelTwoLogSeries q) =
      (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 24 := by
    simpa only [Nat.cast_ofNat, exp_levelTwoLogSeries_eq_product hq1] using
      Complex.exp_nat_mul (levelTwoLogSeries q) 24
  have hsplit : Complex.exp (24 * levelTwoLogSeries q) = P ^ 24 * Complex.exp z := by
    rw [show 24 * levelTwoLogSeries q = 24 * S + z by dsimp only [z]; ring,
      Complex.exp_add]
    have hp : Complex.exp (24 * S) = P ^ 24 := by
      simpa only [Nat.cast_ofNat, hfinite] using Complex.exp_nat_mul S 24
    rw [hp]
  have hdiff : levelTwoHauptmodul q - (-256 * q * P ^ 24) =
      (-256 * q * P ^ 24) * (Complex.exp z - 1) := by
    rw [levelTwoHauptmodul, ← hinf, hsplit]
    ring
  change ‖levelTwoHauptmodul q - (-256 * q * P ^ 24)‖ ≤
    (256 * ‖q‖ * ‖P‖ ^ 24) / 1000000000000000000
  rw [hdiff]
  simp only [norm_mul, norm_neg, Complex.norm_ofNat, norm_pow]
  calc
    _ ≤ (256 * ‖q‖ * ‖P‖ ^ 24) * (1 / 1000000000000000000) :=
      mul_le_mul_of_nonneg_left herr (by positivity)
    _ = _ := by ring

theorem abs_re_levelTwoHauptmodul_add_four_le {q : ℝ}
    (hq : q ∈ Set.Icc 0 (1 / 10000)) :
    |(levelTwoHauptmodul (q : ℂ)).re +
      256 * q * (∏ n ∈ Finset.range 4, (1 + q ^ (n + 1))) ^ 24| ≤
      (256 * q * (∏ n ∈ Finset.range 4, (1 + q ^ (n + 1))) ^ 24) /
        1000000000000000000 := by
  let P : ℝ := ∏ n ∈ Finset.range 4, (1 + q ^ (n + 1))
  have hq0 : 0 ≤ q := hq.1
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact Finset.prod_nonneg (fun n _ => by positivity)
  have hcast : (∏ n ∈ Finset.range 4, (1 + (q : ℂ) ^ (n + 1))) = (P : ℂ) := by
    simp only [P, Complex.ofReal_prod, Complex.ofReal_add, Complex.ofReal_one,
      Complex.ofReal_pow]
  have hpartial : (-256 : ℂ) * (q : ℂ) *
      (∏ n ∈ Finset.range 4, (1 + (q : ℂ) ^ (n + 1))) ^ 24 =
        ((-256 * q * P ^ 24 : ℝ) : ℂ) := by
    rw [hcast]
    push_cast
    rfl
  have hb := norm_levelTwoHauptmodul_sub_four_le (q := (q : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0] using hq.2)
  rw [hpartial, hcast, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hq0, abs_of_nonneg hP0] at hb
  have hr := (Complex.abs_re_le_norm
    (levelTwoHauptmodul (q : ℂ) - ((-256 * q * P ^ 24 : ℝ) : ℂ))).trans hb
  have heq : (levelTwoHauptmodul (q : ℂ) - ((-256 * q * P ^ 24 : ℝ) : ℂ)).re =
      (levelTwoHauptmodul (q : ℂ)).re + 256 * q * P ^ 24 := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    ring
  rw [heq] at hr
  exact hr

private theorem levelTwoHauptmodul_refined_endpoint_bounds :
    -(1 / 72 : ℝ) <
      (levelTwoHauptmodul (5418296542877 / 100000000000000000 : ℂ)).re ∧
    (levelTwoHauptmodul (5418296542878 / 100000000000000000 : ℂ)).re <
      -(1 / 72 : ℝ) := by
  let a : ℝ := 5418296542877 / 100000000000000000
  let b : ℝ := 5418296542878 / 100000000000000000
  have ha := abs_re_levelTwoHauptmodul_add_four_le (q := a) (by norm_num [a])
  have hb := abs_re_levelTwoHauptmodul_add_four_le (q := b) (by norm_num [b])
  have hA : (256 * a * (∏ n ∈ Finset.range 4, (1 + a ^ (n + 1))) ^ 24) *
      (1 + 1 / 1000000000000000000) < (1 / 72 : ℝ) := by
    norm_num [a, Finset.prod_range_succ]
  have hB : (1 / 72 : ℝ) <
      (256 * b * (∏ n ∈ Finset.range 4, (1 + b ^ (n + 1))) ^ 24) *
        (1 - 1 / 1000000000000000000) := by
    norm_num [b, Finset.prod_range_succ]
  have hleft : -(1 / 72 : ℝ) < (levelTwoHauptmodul (a : ℂ)).re := by
    have h := (abs_le.mp ha).1
    linarith
  have hright : (levelTwoHauptmodul (b : ℂ)).re < -(1 / 72 : ℝ) := by
    have h := (abs_le.mp hb).2
    linarith
  constructor
  · simpa only [a, Complex.ofReal_div, Complex.ofReal_ofNat] using hleft
  · simpa only [b, Complex.ofReal_div, Complex.ofReal_ofNat] using hright

theorem levelTwoHauptmodul_real_preimage_refined_bounds {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    q ∈ Set.Icc (5418296542877 / 100000000000000000)
      (5418296542878 / 100000000000000000) := by
  let a : ℝ := 5418296542877 / 100000000000000000
  let b : ℝ := 5418296542878 / 100000000000000000
  let f (x : ℝ) : ℝ := (levelTwoHauptmodul (x : ℂ)).re
  have hmaps : Set.MapsTo (fun x : ℝ => (x : ℂ)) (Set.Icc a b) (Metric.ball 0 1) := by
    intro x hx
    have hx0 : 0 ≤ x := (by norm_num [a] : (0 : ℝ) ≤ a).trans hx.1
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hx0] using hx.2.trans_lt (by norm_num [b] : b < 1)
  have hf : ContinuousOn f (Set.Icc a b) :=
    Complex.continuous_re.comp_continuousOn
      (analyticOnNhd_levelTwoHauptmodul.continuousOn.comp
        Complex.continuous_ofReal.continuousOn hmaps)
  have hend : -(1 / 72 : ℝ) < f a ∧ f b < -(1 / 72 : ℝ) := by
    simpa only [f, a, b, Complex.ofReal_div, Complex.ofReal_ofNat] using
      levelTwoHauptmodul_refined_endpoint_bounds
  obtain ⟨w, hw, hvalue⟩ := intermediate_value_Ioo' (by norm_num [a, b] : a ≤ b)
    hf (show -(1 / 72 : ℝ) ∈ Set.Ioo (f b) (f a) from ⟨hend.2, hend.1⟩)
  have hw0 : 0 < w := (by norm_num [a] : (0 : ℝ) < a).trans hw.1
  have hw1 : |w| < 1 := by
    rw [abs_of_pos hw0]
    exact hw.2.trans (by norm_num [b])
  have hreal : -256 * w * (∏' n : ℕ, (1 + w ^ (n + 1))) ^ 24 = -(1 / 72 : ℝ) := by
    simpa only [f, levelTwoHauptmodul_ofReal hw1, Complex.ofReal_re] using hvalue
  have hwvalue : levelTwoHauptmodul (w : ℂ) = -1 / 72 := by
    rw [levelTwoHauptmodul_ofReal hw1, hreal]
    norm_num
  have hqsmall : ‖(q : ℂ)‖ ≤ 1 / 1000 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq.1]
    exact hq.2.le.trans (by norm_num)
  have hwsmall : ‖(w : ℂ)‖ ≤ 1 / 1000 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
    exact hw.2.le.trans (by norm_num [b])
  have heq : (q : ℂ) = (w : ℂ) := injOn_levelTwoHauptmodul_smallBall
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hqsmall)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hwsmall)
    (hv.trans hwvalue.symm)
  have hqw : q = w := Complex.ofReal_injective heq
  rw [hqw]
  exact ⟨hw.1.le, hw.2.le⟩

end DirichletL
