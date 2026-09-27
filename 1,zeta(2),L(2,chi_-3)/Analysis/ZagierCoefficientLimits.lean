import Arithmetic.ZagierGrowth

/-!
Coefficient limits and polynomial remainders for CDT v2, Section 11.1,
Lemma `defabc` (3), following the case-C recurrence discussed in Zagier
(2009), Section 6, equations (9)-(10). The exact majorants replace the
stronger asymptotic expansion only for this subclaim. See the declaration
-/

namespace DirichletL

open Filter
open scoped Topology

private noncomputable def zagierStepMajorant (n : ℕ) : ℝ :=
  4 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 / 9 ^ (n + 1)

private theorem zagierStepMajorant_nonneg (n : ℕ) : 0 ≤ zagierStepMajorant n := by
  unfold zagierStepMajorant
  positivity

private theorem quartic_le_two_mul_eight_pow (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 ≤ 2 * (8 : ℝ) ^ n := by
  cases n with
  | zero => norm_num
  | succ n =>
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hgap : 0 ≤ 7 * (n : ℝ) ^ 4 + 52 * (n : ℝ) ^ 3 +
          138 * (n : ℝ) ^ 2 + 148 * (n : ℝ) + 47 := by positivity
      have hstep : ((n : ℝ) + 3) ^ 4 ≤ 8 * ((n : ℝ) + 2) ^ 4 := by
        nlinarith
      simp only [Nat.cast_succ] at ih ⊢
      calc
        (((n : ℝ) + 1) + 1 + 1) ^ 4 = ((n : ℝ) + 3) ^ 4 := by ring
        _ ≤ 8 * ((n : ℝ) + 2) ^ 4 := hstep
        _ = 8 * (((n : ℝ) + 1) + 1) ^ 4 := by ring
        _ ≤ 8 * (2 * (8 : ℝ) ^ (n + 1)) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = 2 * (8 : ℝ) ^ (n + 1 + 1) := by rw [pow_succ]; ring

private theorem zagierStepMajorant_add_le (n j : ℕ) :
    zagierStepMajorant (n + j) ≤
      ((8 / 9) * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 / 9 ^ n) * (8 / 9) ^ j := by
  have h1 : ((n + j : ℕ) : ℝ) + 1 ≤ ((n : ℝ) + 1) * ((j : ℝ) + 1) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (Nat.cast_nonneg j)]
  have h2 : ((n + j : ℕ) : ℝ) + 2 ≤ ((n : ℝ) + 2) * ((j : ℝ) + 1) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (Nat.cast_nonneg j)]
  have hpoly : (((n + j : ℕ) : ℝ) + 1) ^ 2 * (((n + j : ℕ) : ℝ) + 2) ^ 2 ≤
      ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 * (2 * (8 : ℝ) ^ j) := by
    calc
      _ ≤ (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2 *
          (((n : ℝ) + 2) * ((j : ℝ) + 1)) ^ 2 := by gcongr
      _ = ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 * ((j : ℝ) + 1) ^ 4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (quartic_le_two_mul_eight_pow j) (by positivity)
  have hp : (9 : ℝ) ^ (n + j + 1) = 9 ^ n * 9 ^ j * 9 := by
    rw [pow_succ, pow_add]
  unfold zagierStepMajorant
  calc
    _ ≤ 4 * (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 * (2 * (8 : ℝ) ^ j)) /
        9 ^ (n + j + 1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ = _ := by rw [hp, div_pow]; field_simp; ring

private theorem summable_zagierStepMajorant : Summable zagierStepMajorant := by
  have hgeom := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 8 / 9) (by norm_num : (8 / 9 : ℝ) < 1)).summable
  apply Summable.of_nonneg_of_le zagierStepMajorant_nonneg _ (hgeom.mul_left (32 / 9))
  intro j
  convert zagierStepMajorant_add_le 0 j using 1 <;> norm_num

private theorem tsum_zagierStepMajorant_add_le (n : ℕ) :
    ∑' j, zagierStepMajorant (n + j) ≤
      8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 / 9 ^ n := by
  have hgeom := hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 8 / 9) (by norm_num : (8 / 9 : ℝ) < 1)
  have hsum := hgeom.mul_left
    ((8 / 9) * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 / 9 ^ n)
  calc
    _ ≤ ∑' j, ((8 / 9) * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 / 9 ^ n) *
        (8 / 9 : ℝ) ^ j :=
      Summable.tsum_le_tsum (zagierStepMajorant_add_le n)
        (summable_zagierStepMajorant.comp_injective (add_right_injective n)) hsum.summable
    _ = _ := by rw [hsum.tsum_eq]; norm_num; ring

/-- Exact bounds on consecutive real ratios from bounded discrete Wronskians. -/
theorem zagier_ratio_step_bounds (v : ℕ → ℚ)
    (hW : ∀ n, 0 ≤ zagierDiscreteWronskian v n ∧ zagierDiscreteWronskian v n ≤ 9 ^ n)
    (n : ℕ) :
    0 ≤ (v (n + 1) : ℝ) / (zagierC (n + 1) : ℝ) - (v n : ℝ) / (zagierC n : ℝ) ∧
      (v (n + 1) : ℝ) / (zagierC (n + 1) : ℝ) - (v n : ℝ) / (zagierC n : ℝ) ≤
        4 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 / 9 ^ (n + 1) := by
  have ha : 0 < (zagierC n : ℝ) := by exact_mod_cast zagierC_pos n
  have hb : 0 < (zagierC (n + 1) : ℝ) := by exact_mod_cast zagierC_pos (n + 1)
  have hw0 : 0 ≤ (zagierDiscreteWronskian v n : ℝ) := by exact_mod_cast (hW n).1
  have hw1 : (zagierDiscreteWronskian v n : ℝ) ≤ 9 ^ n := by exact_mod_cast (hW n).2
  have hr : (v (n + 1) : ℝ) / (zagierC (n + 1) : ℝ) - (v n : ℝ) / (zagierC n : ℝ) =
      (zagierDiscreteWronskian v n : ℝ) / ((zagierC n : ℝ) * (zagierC (n + 1) : ℝ)) := by
    simp only [zagierDiscreteWronskian, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast]
    field_simp
  rw [hr]
  refine ⟨div_nonneg hw0 (mul_pos ha hb).le, ?_⟩
  have h0 : (9 : ℝ) ^ n ≤ 2 * ((n : ℝ) + 1) ^ 2 * (zagierC n : ℝ) := by
    exact_mod_cast nine_pow_le_zagierC_mul n
  have h1 : (9 : ℝ) ^ (n + 1) ≤ 2 * ((n : ℝ) + 2) ^ 2 * (zagierC (n + 1) : ℝ) := by
    convert (show (9 : ℝ) ^ (n + 1) ≤
      2 * (((n + 1 : ℕ) : ℝ) + 1) ^ 2 * (zagierC (n + 1) : ℝ) from
        by exact_mod_cast nine_pow_le_zagierC_mul (n + 1)) using 1
    push_cast
    ring
  calc
    _ ≤ (9 : ℝ) ^ n / ((zagierC n : ℝ) * (zagierC (n + 1) : ℝ)) :=
      div_le_div_of_nonneg_right hw1 (mul_pos ha hb).le
    _ ≤ _ := by
      apply (div_le_div_iff₀ (mul_pos ha hb) (by positivity)).mpr
      have hprod := mul_le_mul h0 h1 (by positivity) (by positivity)
      nlinarith

/-- A bounded discrete Wronskian gives a real coefficient limit and polynomial error. -/
theorem exists_zagier_coefficient_limit (v : ℕ → ℚ)
    (hW : ∀ n, 0 ≤ zagierDiscreteWronskian v n ∧ zagierDiscreteWronskian v n ≤ 9 ^ n) :
    ∃ ℓ : ℝ, Tendsto (fun n => (v n : ℝ) / (zagierC n : ℝ)) atTop (𝓝 ℓ) ∧
      ∀ n, |ℓ * (zagierC n : ℝ) - (v n : ℝ)| ≤
        8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 := by
  let r : ℕ → ℝ := fun n => (v n : ℝ) / (zagierC n : ℝ)
  have hd (n : ℕ) : dist (r n) (r (n + 1)) ≤ zagierStepMajorant n := by
    have h := zagier_ratio_step_bounds v hW n
    rw [dist_comm, Real.dist_eq, abs_of_nonneg h.1]
    exact h.2
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable zagierStepMajorant hd summable_zagierStepMajorant)
  refine ⟨ℓ, hℓ, ?_⟩
  intro n
  have ha : 0 < (zagierC n : ℝ) := by exact_mod_cast zagierC_pos n
  have hu : (zagierC n : ℝ) ≤ (9 : ℝ) ^ n := by exact_mod_cast zagierC_le_nine_pow n
  have htail := (dist_le_tsum_of_dist_le_of_tendsto zagierStepMajorant hd
    summable_zagierStepMajorant hℓ n).trans (tsum_zagierStepMajorant_add_le n)
  have heq : (ℓ - r n) * (zagierC n : ℝ) = ℓ * (zagierC n : ℝ) - (v n : ℝ) := by
    dsimp only [r]
    field_simp
  calc
    _ = |ℓ - r n| * (zagierC n : ℝ) := by rw [← heq, abs_mul, abs_of_pos ha]
    _ = dist (r n) ℓ * (zagierC n : ℝ) := by rw [Real.dist_eq, abs_sub_comm]
    _ ≤ (8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 / 9 ^ n) * (zagierC n : ℝ) :=
      mul_le_mul_of_nonneg_right htail ha.le
    _ ≤ (8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ^ 2 / 9 ^ n) * 9 ^ n :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by field_simp

end DirichletL
