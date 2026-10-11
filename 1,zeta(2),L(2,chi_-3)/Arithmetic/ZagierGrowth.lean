import Arithmetic.ZagierSequences

/-!
Exact growth and recurrence comparison for Zagier sequence C, used for
CDT v2 Section 11.1, Lemma `defabc`, part (3). See
-/

namespace DirichletL

/-- The binomial formula for Zagier C has exponential growth at most `9^n`. -/
theorem zagierC_le_nine_pow (n : ℕ) : zagierC n ≤ 9 ^ n := by
  have hcentral (k : ℕ) : (2 * k).choose k ≤ 4 ^ k := by
    calc
      _ ≤ ∑ j ∈ Finset.range (2 * k + 1), (2 * k).choose j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) (by simp; omega)
      _ = 4 ^ k := by rw [Nat.sum_range_choose, pow_mul]; rfl
  have hbinom : (∑ k ∈ Finset.range (n + 1), n.choose k * 2 ^ k) = 3 ^ n := by
    simpa [mul_comm] using (add_pow (2 : ℕ) 1 n).symm
  calc
    zagierC n ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k * 2 ^ k) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ n.choose k ^ 2 * 4 ^ k := Nat.mul_le_mul_left _ (hcentral k)
        _ = _ := by rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; rfl
    _ ≤ (∑ k ∈ Finset.range (n + 1), n.choose k * 2 ^ k) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = 9 ^ n := by rw [hbinom, ← pow_mul, mul_comm n 2, pow_mul]; rfl

/-- A matching lower exponential bound, up to a quadratic factor. -/
theorem nine_pow_le_zagierC_mul (n : ℕ) : 9 ^ n ≤ 2 * (n + 1) ^ 2 * zagierC n := by
  have hbinom : (∑ k ∈ Finset.range (n + 1), n.choose k * 2 ^ k) = 3 ^ n := by
    simpa [mul_comm] using (add_pow (2 : ℕ) 1 n).symm
  have hsum : (∑ k ∈ Finset.range (n + 1), (n.choose k * 2 ^ k) ^ 2) ≤
      (2 * n + 1) * zagierC n := by
    rw [zagierC, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    calc
      (n.choose k * 2 ^ k) ^ 2 = n.choose k ^ 2 * 4 ^ k := by
        rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
        rfl
      _ ≤ n.choose k ^ 2 * ((2 * k + 1) * (2 * k).choose k) :=
        Nat.mul_le_mul_left _ (Nat.four_pow_le_two_mul_add_one_mul_central_binom k)
      _ ≤ n.choose k ^ 2 * ((2 * n + 1) * (2 * k).choose k) := by gcongr
      _ = (2 * n + 1) * (n.choose k ^ 2 * (2 * k).choose k) := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1))
    (fun _ => (1 : ℕ)) (fun k => n.choose k * 2 ^ k)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, smul_eq_mul,
    mul_one, hbinom] at hcs
  have hpow : (3 ^ n : ℕ) ^ 2 = 9 ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    rfl
  rw [hpow] at hcs
  calc
    9 ^ n ≤ (n + 1) * ∑ k ∈ Finset.range (n + 1), (n.choose k * 2 ^ k) ^ 2 := hcs
    _ ≤ (n + 1) * ((2 * n + 1) * zagierC n) := Nat.mul_le_mul_left _ hsum
    _ ≤ 2 * (n + 1) ^ 2 * zagierC n := by nlinarith

/-- Consecutive Zagier C coefficients grow by at least a factor of three. -/
theorem three_mul_zagierC_le (n : ℕ) : 3 * zagierC n ≤ zagierC (n + 1) := by
  induction n with
  | zero => simp [zagierC_zero, zagierC_one]
  | succ n ih =>
    have hrec := zagierC_recurrence_rational (n := n + 1) (by omega)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hrec
    have hi : 3 * (zagierC n : ℚ) ≤ (zagierC (n + 1) : ℚ) := by exact_mod_cast ih
    have hprev := mul_le_mul_of_nonneg_left hi
      (by positivity : 0 ≤ 3 * ((n : ℚ) + 1) ^ 2)
    have hgap : 0 ≤ 4 * ((n : ℚ) + 1) * ((n : ℚ) + 2) *
        (zagierC (n + 1) : ℚ) := by positivity
    have hc : 3 * (zagierC (n + 1) : ℚ) ≤ (zagierC (n + 1 + 1) : ℚ) := by
      apply (mul_le_mul_left (by positivity : 0 < ((n : ℚ) + 1 + 1) ^ 2)).mp
      nlinarith
    exact_mod_cast hc

/-- A simple lower exponential bound for every Zagier C coefficient. -/
theorem three_pow_le_zagierC (n : ℕ) : 3 ^ n ≤ zagierC n := by
  induction n with
  | zero => simp [zagierC_zero]
  | succ n ih =>
    calc
      3 ^ (n + 1) = 3 * 3 ^ n := by rw [pow_succ, mul_comm]
      _ ≤ 3 * zagierC n := Nat.mul_le_mul_left 3 ih
      _ ≤ zagierC (n + 1) := three_mul_zagierC_le n

theorem zagierC_pos (n : ℕ) : 0 < zagierC n :=
  (pow_pos (by decide : 0 < (3 : ℕ)) n).trans_le (three_pow_le_zagierC n)

/-- The discrete Wronskian of a rational sequence against Zagier C. -/
def zagierDiscreteWronskian (v : ℕ → ℚ) (n : ℕ) : ℚ :=
  (zagierC n : ℚ) * v (n + 1) - (zagierC (n + 1) : ℚ) * v n

/-- The first-order recurrence obtained by subtracting the two case-C equations. -/
theorem zagierDiscreteWronskian_recurrence (v e : ℕ → ℚ)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (n + 1 : ℚ) ^ 2 * v (n + 1) - (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * v n +
        9 * (n : ℚ) ^ 2 * v (n - 1) = e n) (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℚ) ^ 2 * zagierDiscreteWronskian v n =
      9 * (n : ℚ) ^ 2 * zagierDiscreteWronskian v (n - 1) +
        (zagierC n : ℚ) * e n := by
  dsimp only [zagierDiscreteWronskian]
  rw [Nat.sub_add_cancel hn]
  linear_combination (zagierC n : ℚ) * hrec n hn -
    v n * zagierC_recurrence_rational hn

/-- Exact discrete-Wronskian bounds for forcing between zero and one. -/
theorem zagierDiscreteWronskian_bounds (v e : ℕ → ℚ) (hv0 : v 0 = 0) (hv1 : v 1 = 1)
    (he : ∀ n, 1 ≤ n → 0 ≤ e n ∧ e n ≤ 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (n + 1 : ℚ) ^ 2 * v (n + 1) - (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * v n +
        9 * (n : ℚ) ^ 2 * v (n - 1) = e n) (n : ℕ) :
    0 ≤ zagierDiscreteWronskian v n ∧ zagierDiscreteWronskian v n ≤ 9 ^ n := by
  induction n with
  | zero => norm_num [zagierDiscreteWronskian, zagierC_zero, zagierC_one, hv0, hv1]
  | succ n ih =>
    have hr := zagierDiscreteWronskian_recurrence v e hrec (n + 1) (by omega)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hr
    have he0 := (he (n + 1) (by omega)).1
    have he1 := (he (n + 1) (by omega)).2
    have ha0 : 0 ≤ (zagierC (n + 1) : ℚ) := by positivity
    have hc : 0 < ((n : ℚ) + 1 + 1) ^ 2 := by positivity
    have hlow : 0 ≤ 9 * ((n : ℚ) + 1) ^ 2 * zagierDiscreteWronskian v n :=
      mul_nonneg (by positivity) ih.1
    have hforce : (zagierC (n + 1) : ℚ) * e (n + 1) ≤ 9 ^ (n + 1) := by
      calc
        _ ≤ (zagierC (n + 1) : ℚ) * 1 := mul_le_mul_of_nonneg_left he1 ha0
        _ = (zagierC (n + 1) : ℚ) := mul_one _
        _ ≤ 9 ^ (n + 1) := by exact_mod_cast zagierC_le_nine_pow (n + 1)
    have hup := mul_le_mul_of_nonneg_left ih.2
      (by positivity : 0 ≤ 9 * ((n : ℚ) + 1) ^ 2)
    constructor
    · apply (mul_nonneg_iff_of_pos_left hc).mp
      rw [hr]
      exact add_nonneg hlow (mul_nonneg ha0 he0)
    · apply (mul_le_mul_left hc).mp
      have hp : (9 : ℚ) ^ (n + 1) = 9 ^ n * 9 := pow_succ _ _
      rw [hp] at hforce ⊢
      nlinarith [show 0 ≤ ((n : ℚ) + 1) * (9 : ℚ) ^ n by positivity]

/-- Exact comparison for case-C recurrences with forcing between zero and one. -/
theorem zagier_recurrence_comparison (v e : ℕ → ℚ) (hv0 : v 0 = 0) (hv1 : v 1 = 1)
    (he : ∀ n, 1 ≤ n → 0 ≤ e n ∧ e n ≤ 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (n + 1 : ℚ) ^ 2 * v (n + 1) - (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * v n +
        9 * (n : ℚ) ^ 2 * v (n - 1) = e n) :
    ∀ n, 0 ≤ v n ∧ 3 * v n ≤ (n : ℚ) * (zagierC n : ℚ) ∧
      (1 ≤ n → (zagierC n : ℚ) ≤ 3 * v n) := by
  have hW := zagierDiscreteWronskian_bounds v e hv0 hv1 he hrec
  intro n
  induction n with
  | zero => simp [hv0, zagierC_zero]
  | succ n ih =>
    have ha : 0 < (zagierC n : ℚ) := by exact_mod_cast zagierC_pos n
    have ha1 : 0 < (zagierC (n + 1) : ℚ) := by exact_mod_cast zagierC_pos (n + 1)
    have hW0 := (hW n).1
    have hW1 := (hW n).2
    dsimp only [zagierDiscreteWronskian] at hW0 hW1
    have hprod : (3 : ℚ) * 9 ^ n ≤ (zagierC n : ℚ) * (zagierC (n + 1) : ℚ) := by
      have h0 : (3 : ℚ) ^ n ≤ (zagierC n : ℚ) := by exact_mod_cast three_pow_le_zagierC n
      have h1 : (3 : ℚ) ^ (n + 1) ≤ (zagierC (n + 1) : ℚ) := by
        exact_mod_cast three_pow_le_zagierC (n + 1)
      calc
        _ = 3 * ((3 : ℚ) * 3) ^ n := by norm_num
        _ = (3 : ℚ) ^ n * 3 ^ (n + 1) := by rw [mul_pow, pow_succ]; ring
        _ ≤ _ := mul_le_mul h0 h1 (by positivity) ha.le
    have hupper := mul_le_mul_of_nonneg_left ih.2.1 ha1.le
    refine ⟨?_, ?_, ?_⟩
    · apply (mul_nonneg_iff_of_pos_left ha).mp
      nlinarith [mul_nonneg ha1.le ih.1]
    · apply (mul_le_mul_left ha).mp
      simp only [Nat.cast_succ]
      nlinarith
    · intro _
      by_cases hn : n = 0
      · subst n
        norm_num [hv1, zagierC_one]
      · have hlower := mul_le_mul_of_nonneg_left (ih.2.2 (by omega)) ha1.le
        apply (mul_le_mul_left ha).mp
        nlinarith

end DirichletL
