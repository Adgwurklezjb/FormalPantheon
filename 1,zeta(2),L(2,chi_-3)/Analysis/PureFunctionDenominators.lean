import Analysis.MobiusDescentDenominators
import Analysis.PureFunctionIntegrals
import Analysis.JFunctionFactorial
import Arithmetic.FactorialLcm

/-!
The exact coefficient denominator bounds for CDT v2, Lemma `bdenominators`
(supplied TeX 7443-7465), on the literal B2 through B7 series. Positive
degrees retain the paper's extra factors n and 2n-1; zero coefficients
and normalized integration constants are treated explicitly.
-/

namespace DirichletL

theorem isInteger_lcmPrefix_mul_coeff_pureLogarithmSeries (n : ℕ) :
    IsLocalization.IsInteger ℤ
      ((lcmPrefix n : ℚ) * PowerSeries.coeff (R := ℚ) n pureLogarithmSeries) := by
  rw [coeff_pureLogarithmSeries]
  by_cases hn : n = 0
  · subst n
    simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
  obtain ⟨k, hk⟩ := dvd_lcmPrefix (Nat.one_le_iff_ne_zero.mpr hn) le_rfl
  refine ⟨(k : ℤ), ?_⟩
  change (k : ℚ) = _
  rw [hk, Nat.cast_mul]
  field_simp

theorem lcmSqIntegral_pureDilogarithmSeries : LcmSqIntegral pureDilogarithmSeries := by
  intro n
  rw [coeff_pureDilogarithmSeries]
  by_cases hn : n = 0
  · subst n
    simpa using SqIntegral.zero (lcmPrefix 0)
  have h : SqIntegral (1 / (n : ℚ) ^ 2) n := ⟨1, by field_simp; norm_num⟩
  exact h.of_dvd (dvd_lcmPrefix (Nat.one_le_iff_ne_zero.mpr hn) le_rfl)

theorem isInteger_lcmPrefix_mul_coeff_pureB2Series (n : ℕ) :
    IsLocalization.IsInteger ℤ
      ((lcmPrefix (2 * n) : ℚ) * PowerSeries.coeff (R := ℚ) n pureB2Series) := by
  have hx (k : ℕ) : IsLocalization.IsInteger ℤ ((lcmPrefix k : ℚ) *
      PowerSeries.coeff (R := ℚ) k (PowerSeries.X * pureLogarithmSeries)) := by
    simpa only [PowerSeries.map_X, mul_comm] using
      isInteger_lcmPrefix_mul_coeff_mul_map_int
        isInteger_lcmPrefix_mul_coeff_pureLogarithmSeries PowerSeries.X k
  rw [pureB2Series_eq_symmetrizedDescent, map_add, mul_add]
  apply IsLocalization.isInteger_add _
    (isInteger_lcmPrefix_mul_coeff_symmetrizedDescent hx n)
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) 2, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  split_ifs
  · refine ⟨2 * (lcmPrefix (2 * n) : ℤ), ?_⟩
    change ((2 * (lcmPrefix (2 * n) : ℤ) : ℤ) : ℚ) = _
    push_cast
    ring
  · simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))

theorem isInteger_nat_mul_lcmPrefix_mul_coeff_pureB3Series (n : ℕ) :
    IsLocalization.IsInteger ℤ
      (((n * lcmPrefix (2 * n) : ℕ) : ℚ) * PowerSeries.coeff (R := ℚ) n pureB3Series) := by
  cases n with
  | zero => simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
  | succ n =>
    have h := isInteger_lcmPrefix_mul_factorial_quotient n (n + 1)
    rw [show n + (n + 1) + 1 = 2 * (n + 1) by omega] at h
    convert h using 1
    rw [coeff_pureB3Series_succ, pureB3QuotientCoeff, Nat.factorial_succ n]
    rw [show 2 * (n + 1) = 2 * n + 2 by omega]
    push_cast
    ring

theorem sqIntegral_coeff_pureB3Series (n : ℕ) :
    SqIntegral (PowerSeries.coeff (R := ℚ) n pureB3Series) (lcmPrefix (2 * n)) := by
  by_cases hn : n = 0
  · subst n
    simpa using SqIntegral.zero (lcmPrefix 0)
  have hd : n ∣ lcmPrefix (2 * n) :=
    dvd_lcmPrefix (Nat.one_le_iff_ne_zero.mpr hn) (by omega)
  apply (sqIntegral_iff_isInteger _ _).mpr
  simpa only [Nat.cast_pow] using
    isInteger_nat_mul_of_dvd (isInteger_nat_mul_lcmPrefix_mul_coeff_pureB3Series n)
      (show n * lcmPrefix (2 * n) ∣ lcmPrefix (2 * n) ^ 2 by
        simpa only [pow_two] using Nat.mul_dvd_mul_right hd (lcmPrefix (2 * n)))

theorem isInteger_lcmPrefix_mul_odd_mul_coeff_pureB5Series (n : ℕ) :
    IsLocalization.IsInteger ℤ
      ((((2 * n - 1) * lcmPrefix (2 * n) : ℕ) : ℚ) *
        PowerSeries.coeff (R := ℚ) n pureB5Series) := by
  cases n with
  | zero => simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
  | succ n =>
    have h := isInteger_nat_mul_of_dvd (isInteger_lcmPrefix_mul_factorial_quotient n n)
      (lcmPrefix_dvd (show n + n + 1 ≤ 2 * (n + 1) by omega))
    convert h using 1
    rw [coeff_pureB5Series_succ, show 2 * (n + 1) - 1 = 2 * n + 1 by omega,
      show n + n + 1 = 2 * n + 1 by omega]
    push_cast
    field_simp

theorem sqIntegral_coeff_pureB5Series (n : ℕ) :
    SqIntegral (PowerSeries.coeff (R := ℚ) n pureB5Series) (lcmPrefix (2 * n)) := by
  by_cases hn : n = 0
  · subst n
    simpa using SqIntegral.zero (lcmPrefix 0)
  have hd : 2 * n - 1 ∣ lcmPrefix (2 * n) := dvd_lcmPrefix (by omega) (by omega)
  apply (sqIntegral_iff_isInteger _ _).mpr
  simpa only [Nat.cast_pow] using
    isInteger_nat_mul_of_dvd (isInteger_lcmPrefix_mul_odd_mul_coeff_pureB5Series n)
      (show (2 * n - 1) * lcmPrefix (2 * n) ∣ lcmPrefix (2 * n) ^ 2 by
        simpa only [pow_two] using Nat.mul_dvd_mul_right hd (lcmPrefix (2 * n)))

theorem sqIntegral_coeff_pureB4Series (n : ℕ) :
    SqIntegral (PowerSeries.coeff (R := ℚ) n pureB4Series) (lcmPrefix (2 * n)) := by
  have hx : LcmSqIntegral (PowerSeries.X * pureDilogarithmSeries) := by
    simpa only [PowerSeries.map_X, mul_comm] using
      lcmSqIntegral_pureDilogarithmSeries.mul_map_int PowerSeries.X
  have h1 := (sqIntegral_symmetrizedDescent hx n).mul_intCast 2
  have h2 : SqIntegral (PowerSeries.coeff (R := ℚ) n (PowerSeries.X * pureB3Series))
      (lcmPrefix (2 * n)) := by
    cases n with
    | zero => simpa using SqIntegral.zero (lcmPrefix 0)
    | succ n =>
      rw [PowerSeries.coeff_succ_X_mul]
      exact (sqIntegral_coeff_pureB3Series n).of_dvd (lcmPrefix_dvd (by omega))
  rw [pureB4Series, map_sub, PowerSeries.coeff_C_mul]
  simpa only [Int.cast_ofNat, Int.cast_neg, Int.cast_one, mul_neg_one, neg_one_mul,
    ← sub_eq_add_neg, mul_comm] using
    h1.add (h2.mul_intCast (-1))

theorem isInteger_nat_sq_mul_lcmPrefix_mul_coeff_pureB6Series (n : ℕ) :
    IsLocalization.IsInteger ℤ
      (((n ^ 2 * lcmPrefix (2 * n) : ℕ) : ℚ) * PowerSeries.coeff (R := ℚ) n pureB6Series) := by
  cases n with
  | zero => simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
  | succ n =>
    have h := isInteger_nat_mul_div (Nat.succ_ne_zero n)
      (isInteger_nat_mul_lcmPrefix_mul_coeff_pureB3Series (n + 1))
    simpa only [pureB6Series, coeff_formalIntegral_succ, coeff_formalShift,
      Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, pow_two, mul_assoc] using h

theorem isInteger_nat_mul_lcmPrefix_sq_mul_coeff_pureB6Series (n : ℕ) :
    IsLocalization.IsInteger ℤ
      (((n * lcmPrefix (2 * n) ^ 2 : ℕ) : ℚ) * PowerSeries.coeff (R := ℚ) n pureB6Series) := by
  by_cases hn : n = 0
  · subst n
    simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
  apply isInteger_nat_mul_of_dvd (isInteger_nat_sq_mul_lcmPrefix_mul_coeff_pureB6Series n)
  have hd : n ∣ lcmPrefix (2 * n) :=
    dvd_lcmPrefix (Nat.one_le_iff_ne_zero.mpr hn) (by omega)
  simpa only [pow_two, mul_assoc] using
    Nat.mul_dvd_mul_left n (Nat.mul_dvd_mul_right hd (lcmPrefix (2 * n)))

theorem isInteger_nat_mul_lcmPrefix_sq_mul_coeff_pureB7Series (n : ℕ) :
    IsLocalization.IsInteger ℤ
      (((n * lcmPrefix (2 * n) ^ 2 : ℕ) : ℚ) * PowerSeries.coeff (R := ℚ) n pureB7Series) := by
  cases n with
  | zero => simpa using (IsLocalization.isInteger_zero (R := ℤ) (S := ℚ))
  | succ n =>
    have h : IsLocalization.IsInteger ℤ
        (((lcmPrefix (2 * (n + 1)) ^ 2 : ℕ) : ℚ) *
          PowerSeries.coeff (R := ℚ) (n + 1) pureB4Series) := by
      simpa only [Nat.cast_pow] using
        (sqIntegral_iff_isInteger _ _).mp (sqIntegral_coeff_pureB4Series (n + 1))
    simpa only [coeff_pureB7Series_succ, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      isInteger_nat_mul_div (Nat.succ_ne_zero n) h

end DirichletL
