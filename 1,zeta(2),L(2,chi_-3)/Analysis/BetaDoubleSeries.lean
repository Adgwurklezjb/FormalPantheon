import Analysis.BetaLimit

/-!
The absolutely convergent double-series expansion of B in CDT v2,
Section 11.1, supplied `L2chi.tex` line 7673. Product-exponent grouping
into the formal coefficient series is a separate step.
-/

namespace DirichletL

/-- The positive-index geometric expansion of the real beta Lambert series. -/
noncomputable def betaDoubleTerm (q : ℝ) (p : ℕ × ℕ) : ℝ :=
  chiMinusThree (p.1 + 1) / ((p.1 + 1 : ℕ) : ℝ) ^ 2 * (-1 : ℝ) ^ p.2 *
    q ^ ((p.1 + 1) * (p.2 + 1))

theorem norm_betaDoubleTerm_le {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (p : ℕ × ℕ) :
    ‖betaDoubleTerm q p‖ ≤ 1 / ((p.1 + 1 : ℕ) : ℝ) ^ 2 * q ^ p.2 := by
  rcases p with ⟨n, k⟩
  have hcoeff : ‖chiMinusThree (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2‖ ≤
      1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [norm_div, norm_pow, Real.norm_natCast]
    exact div_le_div_of_nonneg_right (norm_chiMinusThree_le_one (n + 1)) (sq_nonneg _)
  have hexp : k ≤ (n + 1) * (k + 1) := by nlinarith
  have hpow : q ^ ((n + 1) * (k + 1)) ≤ q ^ k :=
    pow_le_pow_of_le_one hq₀ hq₁ hexp
  simpa only [betaDoubleTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    mul_one, Real.norm_of_nonneg hq₀] using
    mul_le_mul hcoeff hpow (pow_nonneg hq₀ _) (by positivity)

theorem summable_betaDoubleTerm {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Summable (betaDoubleTerm q) := by
  have hn : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2
      ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  have hk : Summable (fun k : ℕ => q ^ k) := summable_geometric_of_lt_one hq₀ hq₁
  apply Summable.of_norm_bounded
    (g := fun p : ℕ × ℕ => 1 / ((p.1 + 1 : ℕ) : ℝ) ^ 2 * q ^ p.2)
    (hn.mul_of_nonneg hk (by intro n; positivity) (fun k => pow_nonneg hq₀ k))
  exact norm_betaDoubleTerm_le hq₀ hq₁.le

theorem tsum_betaDoubleTerm_row {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (n : ℕ) :
    ∑' k : ℕ, betaDoubleTerm q (n, k) =
      chiMinusThree (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2 *
        (q ^ (n + 1) / (1 + q ^ (n + 1))) := by
  have hterm (k : ℕ) : betaDoubleTerm q (n, k) =
      (chiMinusThree (n + 1) / ((n + 1 : ℕ) : ℝ) ^ 2 * q ^ (n + 1)) *
        (-q ^ (n + 1)) ^ k := by
    dsimp [betaDoubleTerm]
    rw [pow_mul, pow_succ, neg_pow]
    ring
  have hratio : |-q ^ (n + 1)| < 1 := by
    rw [abs_neg, abs_of_nonneg (pow_nonneg hq₀ _)]
    exact pow_lt_one₀ hq₀ hq₁ (Nat.succ_ne_zero n)
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_abs_lt_one hratio]
  simp only [sub_neg_eq_add, div_eq_mul_inv]
  ring

/-- Summing the geometric rows recovers the Lambert formula for B. -/
theorem tsum_betaDoubleTerm {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    ∑' p : ℕ × ℕ, betaDoubleTerm q p = betaLambert q := by
  rw [(summable_betaDoubleTerm hq₀ hq₁).tsum_prod]
  simp_rw [tsum_betaDoubleTerm_row hq₀ hq₁]
  have h := (summable_betaLambert hq₀).tsum_eq_zero_add
  simpa only [betaLambert, chiMinusThree_zero, zero_div, zero_mul, zero_add] using h.symm

end DirichletL
