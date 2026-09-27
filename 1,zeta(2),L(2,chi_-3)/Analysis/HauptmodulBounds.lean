import Arithmetic.PowerSeriesMajorants
import Analysis.Hauptmodul

/-!
Exact exponential coefficient bound for the formal Hauptmodul in CDT v2,
Section 11.1, equation `haupt` (supplied `L2chi.tex` lines 7619-7637).
The bound is used only for local convergence.
-/

namespace DirichletL

theorem abs_coeff_oneSubInv_le_one {k : ℕ} (hk : 0 < k) (n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (oneSubInv k)| ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hnk : n < k
    · rw [coeff_oneSubInv_of_lt hnk]
      split_ifs <;> norm_num
    · have hkn : k ≤ n := Nat.le_of_not_gt hnk
      have hn : n ≠ 0 := by omega
      have he := congrArg (PowerSeries.coeff (R := ℤ) n) (oneSubInv_rightInv hk)
      rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', if_pos hkn,
        PowerSeries.coeff_one, if_neg hn] at he
      rw [sub_eq_zero.mp he]
      exact ih (n - k) (by omega)

theorem abs_coeff_one_sub_X_pow_le_one (k n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (1 - PowerSeries.X ^ k)| ≤ 1 := by
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_X_pow]
  split_ifs <;> norm_num

theorem abs_coeff_hauptFactor_le (i n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (hauptFactor i)| ≤
      PowerSeries.coeff (R := ℤ) n ((PowerSeries.mk 1) ^ 24) := by
  have hnum (k : ℕ) : ∀ m, |PowerSeries.coeff (R := ℤ) m (1 - PowerSeries.X ^ k)| ≤
      PowerSeries.coeff (R := ℤ) m (PowerSeries.mk 1) := by
    intro m
    simpa using abs_coeff_one_sub_X_pow_le_one k m
  have hinv (k : ℕ) (hk : 0 < k) : ∀ m, |PowerSeries.coeff (R := ℤ) m (oneSubInv k)| ≤
      PowerSeries.coeff (R := ℤ) m (PowerSeries.mk 1) := by
    intro m
    simpa using abs_coeff_oneSubInv_le_one hk m
  simpa only [hauptFactor, ← pow_add] using
    abs_coeff_mul_le_of_bounds
      (abs_coeff_mul_le_of_bounds
        (abs_coeff_mul_le_of_bounds
          (abs_coeff_pow_le_of_bounds (hnum (i + 1)) 4)
          (abs_coeff_pow_le_of_bounds (hnum (6 * (i + 1))) 8))
        (abs_coeff_pow_le_of_bounds (hinv (2 * (i + 1)) (by omega)) 8))
      (abs_coeff_pow_le_of_bounds (hinv (3 * (i + 1)) (by omega)) 4) n

theorem abs_coeff_formalProduct_hauptFactor_le (n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n (formalProduct hauptFactor)| ≤ 2 ^ (25 * (n + 1)) := by
  have h := abs_coeff_prod_le_of_bounds (Finset.range (n + 1))
    (fun i _ m => abs_coeff_hauptFactor_le i m) n
  rw [coeff_formalProduct, formalProductCoeff]
  have hbound : |PowerSeries.coeff (R := ℤ) n (∏ i ∈ Finset.range (n + 1), hauptFactor i)| ≤
      PowerSeries.coeff (R := ℤ) n ((PowerSeries.mk 1) ^ (24 * (n + 1))) := by
    simpa only [Finset.prod_const, Finset.card_range, ← pow_mul] using h
  refine hbound.trans ?_
  rw [show 24 * (n + 1) = (24 * n + 23) + 1 by omega,
    PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk]
  have hc := Nat.choose_le_two_pow (24 * n + 23 + n) (24 * n + 23)
  have hp : (2 : ℕ) ^ (24 * n + 23 + n) ≤ 2 ^ (25 * (n + 1)) := by
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  exact_mod_cast hc.trans hp

theorem abs_coeff_hauptmodul_le (n : ℕ) :
    |PowerSeries.coeff (R := ℤ) n hauptmodul| ≤ (2 ^ 25) ^ n := by
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_hauptmodul]
  | succ n =>
    rw [hauptmodul, PowerSeries.coeff_succ_X_mul, ← pow_mul]
    exact abs_coeff_formalProduct_hauptFactor_le n

end DirichletL
