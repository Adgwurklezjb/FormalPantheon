import Analysis.ZagierAuxiliary
import Arithmetic.IntegerDenominators

/-!
Coefficient denominators of the literal G family in CDT v2, Lemma
`Gdenominatortype` and the application following `typesA` (supplied TeX
7874-7877 and 8280-8331). The fixed offset six accounts for three
derivatives; its later asymptotic use needs Remark `rem:overflow`.
-/

namespace DirichletL

theorem sqIntegral_coeff_derivativeFun_of_shift {f : PowerSeries ℚ} {c : ℕ}
    (hf : ∀ n, SqIntegral (PowerSeries.coeff (R := ℚ) n f) (lcmPrefix (2 * n + c)))
    (n : ℕ) :
    SqIntegral (PowerSeries.coeff (R := ℚ) n f.derivativeFun) (lcmPrefix (2 * n + c + 2)) := by
  rw [PowerSeries.coeff_derivativeFun]
  have h := (hf (n + 1)).mul_intCast ((n : ℤ) + 1)
  rw [show 2 * (n + 1) + c = 2 * n + c + 2 by omega] at h
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using h

theorem isInteger_nat_mul_lcmPrefix_sq_mul_coeff_zagierAuxiliary_integral
    {f : PowerSeries ℚ}
    (hf : ∀ n, SqIntegral (PowerSeries.coeff (R := ℚ) n f) (lcmPrefix (2 * n)))
    (i : Fin 3) (n : ℕ) :
    IsLocalization.IsInteger ℤ (((n * lcmPrefix (2 * n + 2) ^ 2 : ℕ) : ℚ) *
      PowerSeries.coeff (R := ℚ) n (zagierAuxiliarySeries f (i.castAdd 4))) := by
  cases n with
  | zero => simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
  | succ n =>
    have h (k : ℕ) (hk : k ≤ n + 2) : IsLocalization.IsInteger ℤ
        ((((n + 1) * lcmPrefix (2 * (n + 1) + 2) ^ 2 : ℕ) : ℚ) *
          (PowerSeries.coeff (R := ℚ) k f / ((n : ℚ) + 1))) := by
      have hs := (hf k).of_dvd (lcmPrefix_dvd (show 2 * k ≤ 2 * (n + 1) + 2 by omega))
      have hi : IsLocalization.IsInteger ℤ
          (((lcmPrefix (2 * (n + 1) + 2) ^ 2 : ℕ) : ℚ) * PowerSeries.coeff (R := ℚ) k f) := by
        simpa only [Nat.cast_pow] using (sqIntegral_iff_isInteger _ _).mp hs
      simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
        isInteger_nat_mul_div (Nat.succ_ne_zero n) hi
    fin_cases i
    · simpa [zagierAuxiliarySeries] using h n (by omega)
    · simpa [zagierAuxiliarySeries] using h (n + 1) (by omega)
    · simpa [zagierAuxiliarySeries] using h (n + 2) le_rfl

theorem sqIntegral_coeff_zagierAuxiliary_derivative {f : PowerSeries ℚ}
    (hf : ∀ n, SqIntegral (PowerSeries.coeff (R := ℚ) n f) (lcmPrefix (2 * n)))
    (i : Fin 4) (n : ℕ) :
    SqIntegral (PowerSeries.coeff (R := ℚ) n (zagierAuxiliarySeries f (i.natAdd 3)))
      (lcmPrefix (2 * n + 6)) := by
  have h1 (k : ℕ) : SqIntegral (PowerSeries.coeff (R := ℚ) k f.derivativeFun)
      (lcmPrefix (2 * k + 2)) := by
    simpa only [Nat.add_zero] using
      sqIntegral_coeff_derivativeFun_of_shift (c := 0) (by simpa using hf) k
  have h2 (k : ℕ) : SqIntegral (PowerSeries.coeff (R := ℚ) k f.derivativeFun.derivativeFun)
      (lcmPrefix (2 * k + 4)) := by
    simpa only [Nat.add_assoc] using sqIntegral_coeff_derivativeFun_of_shift h1 k
  have h3 (k : ℕ) : SqIntegral
      (PowerSeries.coeff (R := ℚ) k f.derivativeFun.derivativeFun.derivativeFun)
      (lcmPrefix (2 * k + 6)) := by
    simpa only [Nat.add_assoc] using sqIntegral_coeff_derivativeFun_of_shift h2 k
  fin_cases i
  · exact (hf n).of_dvd (lcmPrefix_dvd (by omega))
  · exact (h1 n).of_dvd (lcmPrefix_dvd (by omega))
  · exact (h2 n).of_dvd (lcmPrefix_dvd (by omega))
  · exact h3 n

theorem isInteger_nat_pow_mul_lcmPrefix_sq_mul_coeff_zagierAuxiliary
    {f : PowerSeries ℚ}
    (hf : ∀ n, SqIntegral (PowerSeries.coeff (R := ℚ) n f) (lcmPrefix (2 * n)))
    (i : Fin 7) (n : ℕ) :
    IsLocalization.IsInteger ℤ
      (((n ^ (if (i : ℕ) < 3 then 1 else 0) * lcmPrefix (2 * n + 6) ^ 2 : ℕ) : ℚ) *
        PowerSeries.coeff (R := ℚ) n (zagierAuxiliarySeries f i)) := by
  have hI (j : Fin 3) : IsLocalization.IsInteger ℤ
      (((n * lcmPrefix (2 * n + 6) ^ 2 : ℕ) : ℚ) *
        PowerSeries.coeff (R := ℚ) n (zagierAuxiliarySeries f (j.castAdd 4))) := by
    apply isInteger_nat_mul_of_dvd
      (isInteger_nat_mul_lcmPrefix_sq_mul_coeff_zagierAuxiliary_integral hf j n)
    exact Nat.mul_dvd_mul_left n
      (pow_dvd_pow_of_dvd (lcmPrefix_dvd (by omega)) 2)
  have hD (j : Fin 4) : IsLocalization.IsInteger ℤ
      (((lcmPrefix (2 * n + 6) ^ 2 : ℕ) : ℚ) *
        PowerSeries.coeff (R := ℚ) n (zagierAuxiliarySeries f (j.natAdd 3))) := by
    simpa only [Nat.cast_pow] using
      (sqIntegral_iff_isInteger _ _).mp (sqIntegral_coeff_zagierAuxiliary_derivative hf j n)
  fin_cases i
  · simpa [zagierAuxiliarySeries] using hI 0
  · simpa [zagierAuxiliarySeries] using hI 1
  · simpa [zagierAuxiliarySeries] using hI 2
  · simpa [zagierAuxiliarySeries] using hD 0
  · simpa [zagierAuxiliarySeries] using hD 1
  · simpa [zagierAuxiliarySeries] using hD 2
  · simpa [zagierAuxiliarySeries] using hD 3

theorem isInteger_nat_pow_mul_lcmPrefix_sq_mul_coeff_GAuxiliary
    (a b c : ℤ) (i : Fin 7) (n : ℕ) :
    IsLocalization.IsInteger ℤ
      (((n ^ (if (i : ℕ) < 3 then 1 else 0) * lcmPrefix (2 * n + 6) ^ 2 : ℕ) : ℚ) *
        PowerSeries.coeff (R := ℚ) n
          (zagierAuxiliarySeries
            (symmetrizedDescent ((a : ℚ) • hA + (b : ℚ) • hB + (c : ℚ) • hC)) i)) :=
  isInteger_nat_pow_mul_lcmPrefix_sq_mul_coeff_zagierAuxiliary
    (sqIntegral_symmetrizedDescent_h_integer_combination a b c) i n

end DirichletL
