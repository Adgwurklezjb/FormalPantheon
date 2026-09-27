import Analysis.LevelTwoLogarithm

/-!
An exact product tail for CDT v2's signed contour estimate, TeX 8384-8404 and 6947-6948.
-/

namespace DirichletL

/-- The signed logarithmic profile using the first `N` factors of the level-two product. -/
noncomputable def levelTwoLogPartial (N : ℕ) (q : ℂ) : ℝ :=
  8 * Real.log 2 + Real.log ‖q‖ +
    24 * (∑ n ∈ Finset.range N, Complex.log (1 + q ^ (n + 1))).re

theorem levelTwoLogPartial_eq_real (N : ℕ) (q : ℂ) :
    levelTwoLogPartial N q = 8 * Real.log 2 + Real.log ‖q‖ +
      12 * ∑ n ∈ Finset.range N, Real.log (Complex.normSq (1 + q ^ (n + 1))) := by
  have hsum : (∑ n ∈ Finset.range N, Complex.log (1 + q ^ (n + 1))).re =
      ∑ n ∈ Finset.range N, Real.log ‖1 + q ^ (n + 1)‖ := by
    simpa only [Complex.coe_reAddGroupHom, Complex.log_re] using
      map_sum Complex.reAddGroupHom (fun n => Complex.log (1 + q ^ (n + 1))) (Finset.range N)
  dsimp only [levelTwoLogPartial]
  rw [hsum]
  simp_rw [Complex.normSq_eq_norm_sq, Real.log_pow, Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  ring

theorem norm_levelTwoLogSeries_sub_sum_le (N : ℕ) {q : ℂ} {ρ : ℝ}
    (hq : ‖q‖ ≤ ρ) (hρ : ρ < 1) (hhalf : ρ ^ (N + 1) ≤ 1 / 2) :
    ‖levelTwoLogSeries q - ∑ n ∈ Finset.range N, Complex.log (1 + q ^ (n + 1))‖ ≤
      (3 / 2 : ℝ) * ρ ^ (N + 1) / (1 - ρ) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg q).trans hq
  have hs := summable_levelTwoLogSeries (hq.trans_lt hρ)
  have hsplit := hs.sum_add_tsum_nat_add N
  have heq : levelTwoLogSeries q -
      ∑ n ∈ Finset.range N, Complex.log (1 + q ^ (n + 1)) =
        ∑' j : ℕ, Complex.log (1 + q ^ (j + N + 1)) := by
    dsimp only [levelTwoLogSeries]
    linear_combination -hsplit
  rw [heq]
  have hgeom : HasSum (fun j : ℕ => ((3 / 2 : ℝ) * ρ ^ (N + 1)) * ρ ^ j)
      ((3 / 2 : ℝ) * ρ ^ (N + 1) / (1 - ρ)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hρ0 hρ).mul_left ((3 / 2 : ℝ) * ρ ^ (N + 1))
  apply tsum_of_norm_bounded hgeom
  intro j
  have hpow : ‖q ^ (j + N + 1)‖ ≤ ρ ^ (j + N + 1) := by
    simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg q) hq (j + N + 1)
  have hsmall : ‖q ^ (j + N + 1)‖ ≤ 1 / 2 :=
    hpow.trans ((pow_le_pow_of_le_one hρ0 hρ.le
      (show N + 1 ≤ j + N + 1 by omega)).trans hhalf)
  calc
    _ ≤ (3 / 2 : ℝ) * ‖q ^ (j + N + 1)‖ :=
      Complex.norm_log_one_add_half_le_self hsmall
    _ ≤ (3 / 2 : ℝ) * ρ ^ (j + N + 1) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = _ := by rw [Nat.add_assoc, pow_add]; ring

theorem abs_log_norm_levelTwoHauptmodul_sub_partial_le (N : ℕ) {q : ℂ} {ρ : ℝ}
    (hq0 : q ≠ 0) (hq : ‖q‖ ≤ ρ) (hρ : ρ < 1) (hhalf : ρ ^ (N + 1) ≤ 1 / 2) :
    |Real.log ‖levelTwoHauptmodul q‖ - levelTwoLogPartial N q| ≤
      36 * ρ ^ (N + 1) / (1 - ρ) := by
  have htail := norm_levelTwoLogSeries_sub_sum_le N hq hρ hhalf
  have hre := (Complex.abs_re_le_norm
    (levelTwoLogSeries q - ∑ n ∈ Finset.range N, Complex.log (1 + q ^ (n + 1)))).trans htail
  have heq : Real.log ‖levelTwoHauptmodul q‖ - levelTwoLogPartial N q =
      24 * (levelTwoLogSeries q -
        ∑ n ∈ Finset.range N, Complex.log (1 + q ^ (n + 1))).re := by
    rw [log_norm_levelTwoHauptmodul hq0 (hq.trans_lt hρ)]
    simp only [levelTwoLogPartial, Complex.sub_re]
    ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
  have h := mul_le_mul_of_nonneg_left hre (by norm_num : (0 : ℝ) ≤ 24)
  convert h using 1
  ring

theorem cdt_levelTwoLog_tail_bounds :
    (77 / 100 : ℝ) ^ 101 ≤ 1 / 2 ∧
      36 * (77 / 100 : ℝ) ^ 101 / (1 - 77 / 100) < 1 / 100000000 := by
  norm_num

theorem abs_log_norm_levelTwoHauptmodul_sub_partial_100_lt {q : ℂ}
    (hq0 : q ≠ 0) (hq : ‖q‖ ≤ 77 / 100) :
    |Real.log ‖levelTwoHauptmodul q‖ - levelTwoLogPartial 100 q| < 1 / 100000000 := by
  exact (abs_log_norm_levelTwoHauptmodul_sub_partial_le 100 hq0 hq (by norm_num)
    cdt_levelTwoLog_tail_bounds.1).trans_lt cdt_levelTwoLog_tail_bounds.2

end DirichletL
