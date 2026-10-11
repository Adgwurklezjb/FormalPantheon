import Arithmetic.IntegerDenominators

/-!
Exact factorial quotient denominators for CDT v2, Lemma `bdenominators`
(supplied TeX 7443-7465). A finite Pascal identity reduces the coefficient
bounds to divisibility by the positive-prefix lcm.
-/

namespace DirichletL

theorem factorial_quotient_eq_alternating_sum (a b : ℕ) :
    (a.factorial : ℚ) * b.factorial / (a + b + 1).factorial =
      ∑ j ∈ Finset.range (b + 1), (b.choose j : ℚ) *
        ((-1 : ℚ) ^ j / ((a : ℚ) + j + 1)) := by
  induction b generalizing a with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one, mul_one, Nat.add_zero, Nat.zero_add,
      Finset.sum_range_one, Nat.choose_zero_right, pow_zero, Nat.cast_zero, add_zero,
      one_mul]
    rw [Nat.factorial_succ]
    push_cast
    have hap : (a : ℚ) + 1 ≠ 0 := by positivity
    field_simp
  | succ b ih =>
    have hs := Finset.sum_choose_succ_mul
      (fun j (_ : ℕ) => (-1 : ℚ) ^ j / ((a : ℚ) + j + 1)) b
    have hden (j : ℕ) : (a : ℚ) + (j + 1 : ℕ) + 1 =
        ((a + 1 : ℕ) : ℚ) + j + 1 := by
      push_cast
      ring
    simp_rw [pow_succ, mul_neg_one, neg_div, mul_neg, hden] at hs
    rw [Finset.sum_neg_distrib, ← sub_eq_add_neg, ← ih a, ← ih (a + 1)] at hs
    rw [hs]
    rw [show a + (b + 1) + 1 = (a + b + 1) + 1 by omega,
      show a + 1 + b + 1 = (a + b + 1) + 1 by omega,
      Nat.factorial_succ (a + b + 1), Nat.factorial_succ a, Nat.factorial_succ b]
    push_cast
    have hf : ((a + b + 1).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    ring

theorem isInteger_lcmPrefix_mul_factorial_quotient (a b : ℕ) :
    IsLocalization.IsInteger ℤ
      ((lcmPrefix (a + b + 1) : ℚ) *
        ((a.factorial : ℚ) * b.factorial / (a + b + 1).factorial)) := by
  rw [factorial_quotient_eq_alternating_sum]
  apply isInteger_nat_mul_sum
  intro j hj
  have hjb : j ≤ b := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  obtain ⟨k, hk⟩ := dvd_lcmPrefix (n := a + b + 1) (k := a + j + 1)
    (by omega) (by omega)
  refine ⟨(k : ℤ) * (b.choose j : ℤ) * (-1) ^ j, ?_⟩
  change (((k : ℤ) * (b.choose j : ℤ) * (-1) ^ j : ℤ) : ℚ) = _
  rw [hk]
  push_cast
  have hd : (a : ℚ) + j + 1 ≠ 0 := by positivity
  field_simp

end DirichletL
