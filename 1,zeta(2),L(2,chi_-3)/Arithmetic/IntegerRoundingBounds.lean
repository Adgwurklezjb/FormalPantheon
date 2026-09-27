import Mathlib

/-!
Integer rounding for the exact enclosure of CDT v2's integral, TeX 8384-8404.
Meanings and edge cases precede these bodies in
-/

namespace DirichletL

theorem int_ediv_le_real_div (n d : ℤ) (hd : 0 < d) :
    ((n / d : ℤ) : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
  apply (le_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).2
  exact_mod_cast Int.ediv_mul_le n (ne_of_gt hd)

theorem real_div_le_neg_int_ediv_neg (n d : ℤ) (hd : 0 < d) :
    (n : ℝ) / (d : ℝ) ≤ ((-((-n) / d) : ℤ) : ℝ) := by
  have h := int_ediv_le_real_div (-n) d hd
  push_cast at h ⊢
  rw [neg_div] at h
  linarith

theorem int_sqrt_le_real_sqrt (n : ℤ) :
    (Int.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    simpa only [Int.sqrt_natCast, Int.cast_natCast] using Real.nat_sqrt_le_real_sqrt
  · have hn' : n ≤ 0 := le_of_not_ge hn
    simp [Int.sqrt, Int.toNat_of_nonpos hn', Real.sqrt_nonneg]

theorem real_sqrt_le_int_sqrt_add_one (n : ℤ) :
    Real.sqrt (n : ℝ) ≤ (Int.sqrt n : ℝ) + 1 := by
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn
    simpa only [Int.sqrt_natCast, Int.cast_natCast] using Real.real_sqrt_le_nat_sqrt_succ
  · have hn' : n ≤ 0 := le_of_not_ge hn
    have hr : (n : ℝ) ≤ 0 := by exact_mod_cast hn'
    simp [Int.sqrt, Int.toNat_of_nonpos hn', Real.sqrt_eq_zero_of_nonpos hr]

end DirichletL
