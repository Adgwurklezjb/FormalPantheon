import Analysis.ComplexPowerVariation
import Analysis.ComplexLogProfileBounds
import Analysis.LevelTwoLogProfile

/-!
Finite profile variation for CDT v2's signed contour estimate, TeX 8384-8404.
Meanings and all lower-bound hypotheses precede these bodies in
-/

namespace DirichletL

/-- The combined complex linear coefficient of the finite logarithmic profile near a nonzero nome. -/
noncomputable def levelTwoLogSlope (N : ℕ) (q : ℂ) : ℂ :=
  q⁻¹ + 24 * ∑ n ∈ Finset.range N, ((n + 1 : ℕ) : ℂ) * q ^ n / (1 + q ^ (n + 1))

theorem abs_levelTwoLogPartial_sub_le (N : ℕ) (β : ℕ → ℝ) {q q₀ : ℂ} {ρ δ β₀ : ℝ}
    (hq : ‖q‖ ≤ ρ) (hq₀ : ‖q₀‖ ≤ ρ) (hδ : ‖q - q₀‖ ≤ δ)
    (hβ₀ : β₀ ≤ ‖q₀‖) (hδ₀ : δ < β₀)
    (hβ : ∀ n ∈ Finset.range N, β n ≤ ‖1 + q₀ ^ (n + 1)‖)
    (he : ∀ n ∈ Finset.range N, ((n + 1 : ℕ) : ℝ) * ρ ^ n * δ < β n) :
    |levelTwoLogPartial N q - levelTwoLogPartial N q₀| ≤
      ‖levelTwoLogSlope N q₀‖ * δ + δ ^ 2 / (2 * β₀ * (β₀ - δ)) +
        24 * ∑ n ∈ Finset.range N,
          ((((n + 1 : ℕ) : ℝ) * (n : ℝ) / 2) * ρ ^ (n - 1) * δ ^ 2 / β n +
            (((n + 1 : ℕ) : ℝ) * ρ ^ n * δ) ^ 2 /
              (2 * β n * (β n - ((n + 1 : ℕ) : ℝ) * ρ ^ n * δ))) := by
  have hρ : 0 ≤ ρ := (norm_nonneg q).trans hq
  have hδpos : 0 ≤ δ := (norm_nonneg _).trans hδ
  let d : ℂ := q - q₀
  let a (n : ℕ) : ℂ := 1 + q₀ ^ (n + 1)
  let c (n : ℕ) : ℂ := ((n + 1 : ℕ) : ℂ) * q₀ ^ n / a n
  let e (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ) * ρ ^ n * δ
  let p (n : ℕ) : ℝ := (((n + 1 : ℕ) : ℝ) * (n : ℝ) / 2) * ρ ^ (n - 1) * δ ^ 2
  let t (n : ℕ) : ℝ := e n ^ 2 / (2 * β n * (β n - e n))
  let E (n : ℕ) : ℝ :=
    Real.log ‖1 + q ^ (n + 1)‖ - Real.log ‖a n‖ - (c n * d).re
  let E₀ : ℝ := Real.log ‖q‖ - Real.log ‖q₀‖ - (q₀⁻¹ * d).re
  have hE (n : ℕ) (hn : n ∈ Finset.range N) : |E n| ≤ p n / β n + t n := by
    have he0 : 0 ≤ e n := by dsimp only [e]; positivity
    have hb0 : 0 < β n := he0.trans_lt (he n hn)
    have hdiff : (1 + q ^ (n + 1)) - a n = q ^ (n + 1) - q₀ ^ (n + 1) := by
      dsimp only [a]
      ring
    have hpow : ‖q ^ (n + 1) - q₀ ^ (n + 1)‖ ≤ e n := by
      calc
        _ ≤ ((n + 1 : ℕ) : ℝ) * ρ ^ n * ‖q - q₀‖ := by
          simpa only [Nat.add_sub_cancel] using
            norm_pow_sub_pow_le_of_norm_le (n + 1) hq hq₀
        _ ≤ e n := by dsimp only [e]; gcongr
    have hlog := abs_log_norm_sub_sub_re_le (a := a n) (b := 1 + q ^ (n + 1))
      (β := β n) (ε := e n) (hβ n hn) (by simpa only [hdiff] using hpow) (he n hn)
    rw [hdiff] at hlog
    have hpower :
        ‖q ^ (n + 1) - q₀ ^ (n + 1) - ((n + 1 : ℕ) : ℂ) * q₀ ^ n * d‖ ≤ p n := by
      calc
        _ ≤ (((n + 1 : ℕ) : ℝ) * (n : ℝ) / 2) * ρ ^ (n - 1) * ‖q - q₀‖ ^ 2 := by
          simpa only [d, Nat.add_sub_cancel, show n + 1 - 2 = n - 1 by omega] using
            norm_pow_sub_pow_sub_linear_le (n + 1) hq hq₀
        _ ≤ p n := by dsimp only [p]; gcongr
    have hc : ‖(q ^ (n + 1) - q₀ ^ (n + 1)) / a n - c n * d‖ ≤ p n / β n := by
      have heq : (q ^ (n + 1) - q₀ ^ (n + 1)) / a n - c n * d =
          (q ^ (n + 1) - q₀ ^ (n + 1) - ((n + 1 : ℕ) : ℂ) * q₀ ^ n * d) / a n := by
        dsimp only [c]
        simp only [div_eq_mul_inv]
        ring
      rw [heq, norm_div]
      gcongr
      exact hβ n hn
    have hreal := (Complex.abs_re_le_norm
      ((q ^ (n + 1) - q₀ ^ (n + 1)) / a n - c n * d)).trans hc
    calc
      |E n| ≤ |Real.log ‖1 + q ^ (n + 1)‖ - Real.log ‖a n‖ -
            ((q ^ (n + 1) - q₀ ^ (n + 1)) / a n).re| +
          |((q ^ (n + 1) - q₀ ^ (n + 1)) / a n).re - (c n * d).re| :=
        abs_sub_le _ _ _
      _ ≤ t n + p n / β n :=
        add_le_add hlog (by simpa only [Complex.sub_re] using hreal)
      _ = p n / β n + t n := add_comm _ _
  have hE₀ : |E₀| ≤ δ ^ 2 / (2 * β₀ * (β₀ - δ)) := by
    simpa only [E₀, d, div_eq_mul_inv, mul_comm] using
      abs_log_norm_sub_sub_re_le hβ₀ hδ hδ₀
  have re_sum (v : ℕ → ℂ) : (∑ n ∈ Finset.range N, v n).re =
      ∑ n ∈ Finset.range N, (v n).re := by
    simpa only [Complex.coe_reAddGroupHom] using map_sum Complex.reAddGroupHom v (Finset.range N)
  have hslope : (levelTwoLogSlope N q₀ * d).re =
      (q₀⁻¹ * d).re + 24 * ∑ n ∈ Finset.range N, (c n * d).re := by
    change ((q₀⁻¹ + 24 * ∑ n ∈ Finset.range N, c n) * d).re = _
    rw [add_mul, mul_assoc, Finset.sum_mul, Complex.add_re]
    simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, re_sum]
  have heq : levelTwoLogPartial N q - levelTwoLogPartial N q₀ =
      (levelTwoLogSlope N q₀ * d).re + E₀ + 24 * ∑ n ∈ Finset.range N, E n := by
    rw [hslope]
    simp only [levelTwoLogPartial, re_sum, Complex.log_re, E₀, E, a,
      Finset.sum_sub_distrib]
    ring
  have hs : |(levelTwoLogSlope N q₀ * d).re| ≤ ‖levelTwoLogSlope N q₀‖ * δ := by
    calc
      _ ≤ ‖levelTwoLogSlope N q₀ * d‖ := Complex.abs_re_le_norm _
      _ = ‖levelTwoLogSlope N q₀‖ * ‖d‖ := norm_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hδ (norm_nonneg _)
  have hsum : |24 * ∑ n ∈ Finset.range N, E n| ≤
      24 * ∑ n ∈ Finset.range N, (p n / β n + t n) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
    exact mul_le_mul_of_nonneg_left
      ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hE)) (by norm_num)
  rw [heq]
  calc
    _ ≤ |(levelTwoLogSlope N q₀ * d).re| + |E₀| + |24 * ∑ n ∈ Finset.range N, E n| :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ ‖levelTwoLogSlope N q₀‖ * δ + δ ^ 2 / (2 * β₀ * (β₀ - δ)) +
        24 * ∑ n ∈ Finset.range N, (p n / β n + t n) :=
      add_le_add (add_le_add hs hE₀) hsum

end DirichletL
