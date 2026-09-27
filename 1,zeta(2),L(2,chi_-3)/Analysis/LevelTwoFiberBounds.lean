import Analysis.LevelTwoLogTail
import Analysis.DedekindEtaScaling

/-!
Exact disc estimates for the specialized exceptional fiber in CDT author
Lemma A.4.4, page 205, with product normalization on page 204.
Meanings and endpoint checks precede these bodies in
-/

namespace DirichletL

theorem mul_norm_le_norm_levelTwoHauptmodul {q : ℂ} (hq : ‖q‖ ≤ 1 / 100) :
    64 * ‖q‖ ≤ ‖levelTwoHauptmodul q‖ := by
  have hlog : ‖levelTwoLogSeries q‖ ≤ 1 / 66 := by
    have h := norm_levelTwoLogSeries_sub_sum_le 0 hq (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hmul : ‖24 * levelTwoLogSeries q‖ ≤ 4 / 11 := by
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  have hsub : ‖Complex.exp (24 * levelTwoLogSeries q) - 1‖ ≤ 8 / 11 := by
    have h := Complex.norm_exp_sub_one_le (hmul.trans (by norm_num))
    linarith
  have hlower : (1 / 4 : ℝ) ≤ ‖Complex.exp (24 * levelTwoLogSeries q)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (Complex.exp (24 * levelTwoLogSeries q))
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hexp : Complex.exp (24 * levelTwoLogSeries q) =
      (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 24 := by
    simpa only [Nat.cast_ofNat,
      exp_levelTwoLogSeries_eq_product (hq.trans_lt (by norm_num))] using
      Complex.exp_nat_mul (levelTwoLogSeries q) 24
  rw [levelTwoHauptmodul, ← hexp, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
  calc
    64 * ‖q‖ = 256 * ‖q‖ * (1 / 4) := by ring
    _ ≤ 256 * ‖q‖ * ‖Complex.exp (24 * levelTwoLogSeries q)‖ :=
      mul_le_mul_of_nonneg_left hlower (by positivity)

theorem norm_levelTwoHauptmodul_le_sevenHundred {q : ℂ} (hq : ‖q‖ ≤ 1 / 12) :
    ‖levelTwoHauptmodul q‖ ≤ 700 := by
  have hlog : ‖levelTwoLogSeries q‖ ≤ 3 / 22 := by
    have h := norm_levelTwoLogSeries_sub_sum_le 0 hq (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hmul : ‖24 * levelTwoLogSeries q‖ ≤ 10 / 3 := by
    rw [norm_mul, Complex.norm_ofNat]
    linarith
  have hre : (24 * levelTwoLogSeries q).re ≤ 10 / 3 :=
    (Complex.re_le_norm _).trans hmul
  have hone : Real.exp 1 ≤ 11 / 4 := by linarith [Real.exp_one_lt_d9]
  have hthird : Real.exp (1 / 3) ≤ 3 / 2 := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num)
    norm_num at h ⊢
    exact h
  have hthree : Real.exp 3 = Real.exp 1 ^ 3 := by
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 3
  have hten : Real.exp (10 / 3) ≤ (11 / 4 : ℝ) ^ 3 * (3 / 2) := by
    calc
      _ = Real.exp 1 ^ 3 * Real.exp (1 / 3) := by
        rw [show (10 / 3 : ℝ) = 3 + 1 / 3 by norm_num, Real.exp_add, hthree]
      _ ≤ (11 / 4 : ℝ) ^ 3 * (3 / 2) :=
        mul_le_mul (pow_le_pow_left₀ (Real.exp_pos 1).le hone 3)
          hthird (Real.exp_pos _).le (by positivity)
  have he : Real.exp (24 * levelTwoLogSeries q).re ≤ (11 / 4 : ℝ) ^ 3 * (3 / 2) :=
    (Real.exp_le_exp.mpr hre).trans hten
  have hexp : Complex.exp (24 * levelTwoLogSeries q) =
      (∏' n : ℕ, (1 + q ^ (n + 1))) ^ 24 := by
    simpa only [Nat.cast_ofNat,
      exp_levelTwoLogSeries_eq_product (hq.trans_lt (by norm_num))] using
      Complex.exp_nat_mul (levelTwoLogSeries q) 24
  rw [levelTwoHauptmodul, ← hexp, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat,
    Complex.norm_exp]
  calc
    _ ≤ 256 * (1 / 12) * ((11 / 4 : ℝ) ^ 3 * (3 / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num))
        he (Real.exp_pos _).le (by positivity)
    _ ≤ 700 := by norm_num

theorem norm_qParam_one_half_le_of_im_ge {τ : ℂ} (hτ : 5 / 6 ≤ τ.im) :
    ‖Function.Periodic.qParam 1 (τ / 2)‖ ≤ 1 / 12 := by
  have hseries : (12 : ℝ) < Real.exp (5 / 2) := by
    calc
      _ < ∑ m ∈ Finset.range 7, (5 / 2 : ℝ) ^ m / (m.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ]
      _ ≤ Real.exp (5 / 2) := Real.sum_le_exp_of_nonneg (by norm_num) 7
  have he : (12 : ℝ) < Real.exp (5 * Real.pi / 6) :=
    hseries.trans (Real.exp_lt_exp.mpr (by linarith [Real.pi_gt_d2]))
  have hrecip : Real.exp (-(5 * Real.pi / 6)) ≤ 1 / 12 := by
    rw [Real.exp_neg, ← one_div]
    exact (one_div_lt_one_div_of_lt (by norm_num) he).le
  rw [Function.Periodic.norm_qParam]
  simp only [Complex.div_ofNat_im, div_one]
  calc
    _ ≤ Real.exp (-(5 * Real.pi / 6)) := Real.exp_le_exp.mpr (by
      have h := mul_le_mul_of_nonneg_left hτ Real.pi_pos.le
      nlinarith)
    _ ≤ 1 / 12 := hrecip

theorem norm_qParam_one_le_of_im_ge {τ : ℂ} (hτ : 5 / 6 ≤ τ.im) :
    ‖Function.Periodic.qParam 1 τ‖ ≤ 1 / 100 := by
  have h := qParam_one_nat_mul 2 (τ / 2)
  norm_num only [Nat.cast_ofNat] at h
  rw [show (2 : ℂ) * (τ / 2) = τ by ring] at h
  rw [h, norm_pow]
  calc
    _ ≤ (1 / 12 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
      (norm_qParam_one_half_le_of_im_ge hτ) 2
    _ ≤ 1 / 100 := by norm_num

end DirichletL
