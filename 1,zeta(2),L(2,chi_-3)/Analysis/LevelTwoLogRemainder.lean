import Analysis.LevelTwoLogRecurrences

/-!
Accumulated nonlinear errors for CDT v2's finite profile, TeX 8384-8404.
Meanings and every strict denominator margin precede these bodies in
-/

namespace DirichletL

/-- The finite profile difference after subtracting its combined complex linear term. -/
noncomputable def levelTwoLogRemainder (n : ℕ) (q q₀ : ℂ) : ℝ :=
  levelTwoLogPartial n q - levelTwoLogPartial n q₀ -
    (levelTwoLogSlope n q₀ * (q - q₀)).re

theorem levelTwoLogRemainder_zero (q q₀ : ℂ) :
    levelTwoLogRemainder 0 q q₀ = Real.log ‖q‖ - Real.log ‖q₀‖ -
      (q₀⁻¹ * (q - q₀)).re := by
  simp only [levelTwoLogRemainder, levelTwoLogPartial, levelTwoLogSlope,
    Finset.sum_range_zero, Complex.zero_re, mul_zero, add_zero]
  ring

theorem levelTwoLogRemainder_succ (n : ℕ) (q q₀ : ℂ) :
    levelTwoLogRemainder (n + 1) q q₀ = levelTwoLogRemainder n q q₀ +
      24 * (Real.log ‖1 + q ^ (n + 1)‖ - Real.log ‖1 + q₀ ^ (n + 1)‖ -
        ((((n + 1 : ℕ) : ℂ) * q₀ ^ n / (1 + q₀ ^ (n + 1))) * (q - q₀)).re) := by
  dsimp only [levelTwoLogRemainder]
  rw [levelTwoLogPartial_succ, levelTwoLogPartial_succ, levelTwoLogSlope_succ]
  have hc : (24 * ((n + 1 : ℕ) : ℂ) * q₀ ^ n / (1 + q₀ ^ (n + 1))) * (q - q₀) =
      24 * ((((n + 1 : ℕ) : ℂ) * q₀ ^ n / (1 + q₀ ^ (n + 1))) * (q - q₀)) := by ring
  rw [add_mul, Complex.add_re, hc]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  ring

theorem abs_log_pow_factor_remainder_le (n : ℕ) {q q₀ : ℂ} {ρ δ β ε p : ℝ}
    (hq : ‖q‖ ≤ ρ) (hq₀ : ‖q₀‖ ≤ ρ) (hδ : ‖q - q₀‖ ≤ δ)
    (hβ : β ≤ ‖1 + q₀ ^ (n + 1)‖)
    (hε : ((n + 1 : ℕ) : ℝ) * ρ ^ n * δ ≤ ε)
    (hp : (((n + 1 : ℕ) : ℝ) * (n : ℝ) / 2) * ρ ^ (n - 1) * δ ^ 2 ≤ p)
    (hsmall : ε < β) :
    |Real.log ‖1 + q ^ (n + 1)‖ - Real.log ‖1 + q₀ ^ (n + 1)‖ -
      ((((n + 1 : ℕ) : ℂ) * q₀ ^ n / (1 + q₀ ^ (n + 1))) * (q - q₀)).re| ≤
      p / β + ε ^ 2 / (2 * β * (β - ε)) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg q).trans hq
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδ
  have hε0 : 0 ≤ ε := (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ) * ρ ^ n * δ).trans hε
  have hβ0 : 0 < β := hε0.trans_lt hsmall
  have hpow : ‖q ^ (n + 1) - q₀ ^ (n + 1)‖ ≤ ε := by
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) * ρ ^ n * ‖q - q₀‖ := by
        simpa only [Nat.add_sub_cancel] using
          norm_pow_sub_pow_le_of_norm_le (n + 1) hq hq₀
      _ ≤ ((n + 1 : ℕ) : ℝ) * ρ ^ n * δ := by gcongr
      _ ≤ ε := hε
  have hpower :
      ‖q ^ (n + 1) - q₀ ^ (n + 1) - ((n + 1 : ℕ) : ℂ) * q₀ ^ n * (q - q₀)‖ ≤ p := by
    calc
      _ ≤ (((n + 1 : ℕ) : ℝ) * (n : ℝ) / 2) * ρ ^ (n - 1) * ‖q - q₀‖ ^ 2 := by
        simpa only [Nat.add_sub_cancel, show n + 1 - 2 = n - 1 by omega] using
          norm_pow_sub_pow_sub_linear_le (n + 1) hq hq₀
      _ ≤ (((n + 1 : ℕ) : ℝ) * (n : ℝ) / 2) * ρ ^ (n - 1) * δ ^ 2 := by gcongr
      _ ≤ p := hp
  have hp0 : 0 ≤ p := (norm_nonneg _).trans hpower
  have hdiff : (1 + q ^ (n + 1)) - (1 + q₀ ^ (n + 1)) =
      q ^ (n + 1) - q₀ ^ (n + 1) := by ring
  have hlog := abs_log_norm_sub_sub_re_le (b := 1 + q ^ (n + 1)) hβ
    (by simpa only [hdiff] using hpow) hsmall
  rw [hdiff] at hlog
  have hc : ‖(q ^ (n + 1) - q₀ ^ (n + 1)) / (1 + q₀ ^ (n + 1)) -
      (((n + 1 : ℕ) : ℂ) * q₀ ^ n / (1 + q₀ ^ (n + 1))) * (q - q₀)‖ ≤ p / β := by
    have heq : (q ^ (n + 1) - q₀ ^ (n + 1)) / (1 + q₀ ^ (n + 1)) -
        (((n + 1 : ℕ) : ℂ) * q₀ ^ n / (1 + q₀ ^ (n + 1))) * (q - q₀) =
        (q ^ (n + 1) - q₀ ^ (n + 1) - ((n + 1 : ℕ) : ℂ) * q₀ ^ n * (q - q₀)) /
          (1 + q₀ ^ (n + 1)) := by ring
    rw [heq, norm_div]
    gcongr
  have hreal := (Complex.abs_re_le_norm _).trans hc
  calc
    _ ≤ |Real.log ‖1 + q ^ (n + 1)‖ - Real.log ‖1 + q₀ ^ (n + 1)‖ -
          ((q ^ (n + 1) - q₀ ^ (n + 1)) / (1 + q₀ ^ (n + 1))).re| +
        |((q ^ (n + 1) - q₀ ^ (n + 1)) / (1 + q₀ ^ (n + 1))).re -
          ((((n + 1 : ℕ) : ℂ) * q₀ ^ n / (1 + q₀ ^ (n + 1))) * (q - q₀)).re| :=
      abs_sub_le _ _ _
    _ ≤ ε ^ 2 / (2 * β * (β - ε)) + p / β :=
      add_le_add hlog (by simpa only [Complex.sub_re] using hreal)
    _ = _ := add_comm _ _

end DirichletL
