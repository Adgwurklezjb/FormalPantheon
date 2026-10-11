import Analysis.LevelTwoLogTail
import Analysis.LevelTwoRealPreimage

/-!
Exact bounds for the positive root used in CDT author Lemma A.4.4,
page 205, with the product normalization recalled on page 204.
Meanings and endpoint checks precede the bodies in
-/

namespace DirichletL

theorem norm_levelTwoHauptmodul_le_mul {q : ℂ} (hq : ‖q‖ ≤ 1 / 10000) :
    ‖levelTwoHauptmodul q‖ ≤ 258 * ‖q‖ := by
  have hlog : ‖levelTwoLogSeries q‖ ≤ 1 / 6666 := by
    have h := norm_levelTwoLogSeries_sub_sum_le 0 hq (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hmul : ‖24 * levelTwoLogSeries q‖ ≤ 4 / 1111 := by
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  have hsub : ‖Complex.exp (24 * levelTwoLogSeries q) - 1‖ ≤ 8 / 1111 := by
    have h := Complex.norm_exp_sub_one_le (hmul.trans (by norm_num))
    linarith
  have hbound : ‖Complex.exp (24 * levelTwoLogSeries q)‖ ≤ 1119 / 1111 := by
    calc
      _ = ‖(Complex.exp (24 * levelTwoLogSeries q) - 1) + 1‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖Complex.exp (24 * levelTwoLogSeries q) - 1‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
      _ ≤ 1119 / 1111 := by rw [norm_one]; linarith
  have hexp : Complex.exp (24 * levelTwoLogSeries q) =
      (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 24 := by
    simpa only [Nat.cast_ofNat,
      exp_levelTwoLogSeries_eq_product (hq.trans_lt (by norm_num))] using
      Complex.exp_nat_mul (levelTwoLogSeries q) 24
  rw [levelTwoHauptmodul, ← hexp, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
  calc
    _ ≤ 256 * ‖q‖ * (1119 / 1111) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ 258 * ‖q‖ := by nlinarith [norm_nonneg q]

theorem levelTwoHauptmodul_real_preimage_bounds {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    q ∈ Set.Icc (1 / 18576) (1 / 18432) := by
  have hnorm := norm_levelTwoHauptmodul_le_mul (q := (q : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq.1] using hq.2.le)
  rw [hv, norm_div, norm_neg, norm_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq.1] at hnorm
  have hreal := levelTwoHauptmodul_ofReal_le hq.1.le (hq.2.trans (by norm_num))
  rw [hv] at hreal
  norm_num at hreal
  constructor <;> linarith

theorem levelTwoHauptmodul_real_preimage_height_bounds {q : ℝ}
    (hq : q ∈ Set.Ioo 0 (1 / 10000))
    (hv : levelTwoHauptmodul (q : ℂ) = -1 / 72) :
    (Function.Periodic.invQParam 1 (q : ℂ)).im ∈ Set.Icc (3 / 2) (8 / 5) := by
  have hqbound := levelTwoHauptmodul_real_preimage_bounds hq hv
  have heupper : Real.exp 1 ≤ 11 / 4 := by linarith [Real.exp_one_lt_d9]
  have helower : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hehalf : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    norm_num at h ⊢
    exact h
  have he9 : Real.exp 9 = Real.exp 1 ^ 9 := by
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 9
  have he10 : Real.exp 10 = Real.exp 1 ^ 10 := by
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 10
  have hexplo : Real.exp (3 * Real.pi) < 18432 := by
    calc
      _ < Real.exp (19 / 2) := Real.exp_lt_exp.mpr (by linarith [Real.pi_lt_d2])
      _ = Real.exp 1 ^ 9 * Real.exp (1 / 2) := by
        rw [show (19 / 2 : ℝ) = 9 + 1 / 2 by norm_num, Real.exp_add, he9]
      _ ≤ (11 / 4 : ℝ) ^ 9 * 2 :=
        mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le heupper 9)
          hehalf (Real.exp_pos _).le (by positivity)
      _ < 18432 := by norm_num
  have hexphi : (18576 : ℝ) < Real.exp (16 * Real.pi / 5) := by
    calc
      _ < (27 / 10 : ℝ) ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) helower 10
      _ = Real.exp 10 := he10.symm
      _ < Real.exp (16 * Real.pi / 5) :=
        Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_d2])
  have hloglo : 3 * Real.pi < Real.log 18432 :=
    (Real.lt_log_iff_exp_lt (by norm_num)).mpr hexplo
  have hloghi : Real.log 18576 < 16 * Real.pi / 5 :=
    (Real.log_lt_iff_lt_exp (by norm_num)).mpr hexphi
  have hqupper := Real.log_le_log hq.1 hqbound.2
  have hqlower := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 18576) hqbound.1
  simp only [one_div, Real.log_inv] at hqupper hqlower
  rw [Function.Periodic.im_invQParam, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hq.1]
  have hden : 0 < 2 * Real.pi := by positivity
  have heq : -(1 : ℝ) / (2 * Real.pi) * Real.log q = -Real.log q / (2 * Real.pi) := by
    ring
  rw [heq]
  constructor
  · apply (le_div_iff₀ hden).mpr
    linarith
  · apply (div_le_iff₀ hden).mpr
    linarith

end DirichletL
