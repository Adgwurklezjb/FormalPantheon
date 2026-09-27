import Analysis.CharacterGeometric

/-!
The uncorrected dilogarithm double expansion underlying C in CDT v2,
Section 11.1, supplied `L2chi.tex` lines 7674-7675. The correction at q^2
and grouping into formal coefficients are separate steps.
-/

namespace DirichletL

/-- The positive-index double expansion of the uncorrected gamma series. -/
noncomputable def gammaDoubleTerm (q : ℝ) (p : ℕ × ℕ) : ℝ :=
  chiMinusThree (p.1 + 1) / ((p.2 + 1 : ℕ) : ℝ) ^ 2 *
    q ^ ((p.1 + 1) * (p.2 + 1))

theorem norm_gammaDoubleTerm_le {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (p : ℕ × ℕ) :
    ‖gammaDoubleTerm q p‖ ≤ 1 / ((p.2 + 1 : ℕ) : ℝ) ^ 2 * q ^ p.1 := by
  rcases p with ⟨n, k⟩
  have hcoeff : ‖chiMinusThree (n + 1) / ((k + 1 : ℕ) : ℝ) ^ 2‖ ≤
      1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
    rw [norm_div, norm_pow, Real.norm_natCast]
    exact div_le_div_of_nonneg_right (norm_chiMinusThree_le_one (n + 1)) (sq_nonneg _)
  have hexp : n ≤ (n + 1) * (k + 1) := by nlinarith
  have hpow : q ^ ((n + 1) * (k + 1)) ≤ q ^ n :=
    pow_le_pow_of_le_one hq₀ hq₁ hexp
  simpa only [gammaDoubleTerm, norm_mul, norm_pow, Real.norm_of_nonneg hq₀] using
    mul_le_mul hcoeff hpow (pow_nonneg hq₀ _) (by positivity)

theorem summable_gammaDoubleTerm {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Summable (gammaDoubleTerm q) := by
  have hn : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq₀ hq₁
  have hk : Summable (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2
      ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  have hbound : Summable (fun p : ℕ × ℕ =>
      1 / ((p.2 + 1 : ℕ) : ℝ) ^ 2 * q ^ p.1) := by
    simpa only [mul_comm] using
      hn.mul_of_nonneg hk (fun n => pow_nonneg hq₀ n) (by intro k; positivity)
  apply Summable.of_norm_bounded hbound
  exact norm_gammaDoubleTerm_le hq₀ hq₁.le

/-- The Lambert form of the uncorrected real gamma series. -/
noncomputable def gammaLambertBase (q : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / (k : ℝ) ^ 2 * (q ^ k / (1 + q ^ k + (q ^ k) ^ 2))

theorem norm_gammaLambertBase_summand_le {q : ℝ} (hq : 0 ≤ q) (k : ℕ) :
    ‖1 / (k : ℝ) ^ 2 * (q ^ k / (1 + q ^ k + (q ^ k) ^ 2))‖ ≤
      1 / (k : ℝ) ^ 2 := by
  have hpow : 0 ≤ q ^ k := pow_nonneg hq k
  have hden : 0 < 1 + q ^ k + (q ^ k) ^ 2 := by positivity
  have hratio_nonneg : 0 ≤ q ^ k / (1 + q ^ k + (q ^ k) ^ 2) :=
    div_nonneg hpow hden.le
  have hratio_le : q ^ k / (1 + q ^ k + (q ^ k) ^ 2) ≤ 1 :=
    (div_le_one hden).2 (by nlinarith [sq_nonneg (q ^ k)])
  calc
    _ = (1 / (k : ℝ) ^ 2) * (q ^ k / (1 + q ^ k + (q ^ k) ^ 2)) := by
      rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ 1 / (k : ℝ) ^ 2),
        Real.norm_of_nonneg hratio_nonneg]
    _ ≤ (1 / (k : ℝ) ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hratio_le (by positivity)
    _ = _ := mul_one _

theorem summable_gammaLambertBase {q : ℝ} (hq : 0 ≤ q) :
    Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2 *
      (q ^ k / (1 + q ^ k + (q ^ k) ^ 2))) := by
  apply Summable.of_norm_bounded (g := fun k : ℕ => 1 / (k : ℝ) ^ 2)
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  exact norm_gammaLambertBase_summand_le hq

theorem tsum_gammaDoubleTerm_column {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) (k : ℕ) :
    ∑' n : ℕ, gammaDoubleTerm q (n, k) =
      1 / ((k + 1 : ℕ) : ℝ) ^ 2 *
        (q ^ (k + 1) / (1 + q ^ (k + 1) + (q ^ (k + 1)) ^ 2)) := by
  have hp₀ : 0 ≤ q ^ (k + 1) := pow_nonneg hq₀ _
  have hp₁ : q ^ (k + 1) < 1 := pow_lt_one₀ hq₀ hq₁ (Nat.succ_ne_zero k)
  have hs := hasSum_chiMinusThree_mul_pow hp₀ hp₁
  have hshift :
      ∑' n : ℕ, chiMinusThree (n + 1) * (q ^ (k + 1)) ^ (n + 1) =
        q ^ (k + 1) / (1 + q ^ (k + 1) + (q ^ (k + 1)) ^ 2) := by
    have h := hs.summable.tsum_eq_zero_add
    rw [hs.tsum_eq] at h
    simpa only [chiMinusThree_zero, zero_mul, zero_add] using h.symm
  have hterm (n : ℕ) : gammaDoubleTerm q (n, k) =
      (1 / ((k + 1 : ℕ) : ℝ) ^ 2) *
        (chiMinusThree (n + 1) * (q ^ (k + 1)) ^ (n + 1)) := by
    dsimp [gammaDoubleTerm]
    rw [← pow_mul, Nat.mul_comm (k + 1) (n + 1)]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, hshift]

/-- Summing the character columns recovers the gamma Lambert base. -/
theorem tsum_gammaDoubleTerm {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    ∑' p : ℕ × ℕ, gammaDoubleTerm q p = gammaLambertBase q := by
  have hs := summable_gammaDoubleTerm hq₀ hq₁
  calc
    _ = ∑' n : ℕ, ∑' k : ℕ, gammaDoubleTerm q (n, k) := hs.tsum_prod
    _ = ∑' k : ℕ, ∑' n : ℕ, gammaDoubleTerm q (n, k) :=
      (Summable.tsum_comm (f := fun n k => gammaDoubleTerm q (n, k)) hs).symm
    _ = ∑' k : ℕ, 1 / ((k + 1 : ℕ) : ℝ) ^ 2 *
        (q ^ (k + 1) / (1 + q ^ (k + 1) + (q ^ (k + 1)) ^ 2)) := by
      simp_rw [tsum_gammaDoubleTerm_column hq₀ hq₁]
    _ = _ := by
      have h := (summable_gammaLambertBase hq₀).tsum_eq_zero_add
      simpa only [gammaLambertBase, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
        div_zero, zero_mul, zero_add] using h.symm

end DirichletL
