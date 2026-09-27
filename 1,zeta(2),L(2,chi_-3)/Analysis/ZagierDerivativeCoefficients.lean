import Analysis.HauptmodulDifferential
import Analysis.HauptmodulEulerProduct
import Arithmetic.PowerSeriesEuler

/-!
Finite exact q-coefficients for the normalized Hauptmodul derivative identity
in Zagier (2009), Section 5, equation (7). These are formal statements only;
the analytic transfer to the upper half-plane is a separate obligation.
-/

namespace DirichletL

private theorem coeff_qEulerProductSeries (d n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (qEulerProductSeries d) =
      PowerSeries.coeff (R := ℤ) n
        (∏ i ∈ Finset.range (n + 1), (1 - PowerSeries.X ^ (d * (i + 1)))) := by
  simp only [qEulerProductSeries, coeff_formalProduct, formalProductCoeff]

theorem coeff_zero_qEulerProductSeries (d : ℕ) (hd : 0 < d) :
    PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries d) = 1 := by
  rw [coeff_qEulerProductSeries d 0]
  have hd0 : d ≠ 0 := by omega
  norm_num [PowerSeries.coeff_one, PowerSeries.coeff_X_pow, hd0]

theorem coeff_one_qEulerProductSeries (d : ℕ) (hd : 0 < d) :
    PowerSeries.coeff (R := ℤ) 1 (qEulerProductSeries d) =
      if d = 1 then -1 else 0 := by
  rw [coeff_qEulerProductSeries d 1]
  simp [Finset.prod_range_succ, PowerSeries.coeff_mul,
    PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
    Finset.Nat.antidiagonal_eq_map, Finset.sum_map, Finset.sum_range_succ]
  by_cases h : d = 1
  · simp [h]
  · have hd2 : 2 ≤ d := by omega
    have h1d2 : 1 ≠ d * 2 := by omega
    simp [h, hd2, h1d2]
    omega

theorem coeff_two_qEulerProductSeries (d : ℕ) (hd : 0 < d) :
    PowerSeries.coeff (R := ℤ) 2 (qEulerProductSeries d) =
      if d = 1 then -1 else if d = 2 then -1 else 0 := by
  rw [coeff_qEulerProductSeries d 2]
  simp [Finset.prod_range_succ, PowerSeries.coeff_mul,
    PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
    Finset.Nat.antidiagonal_eq_map, Finset.sum_map, Finset.sum_range_succ]
  by_cases h1 : d = 1
  · simp [h1]
  by_cases h2 : d = 2
  · simp [h1, h2]
  · have hd3 : 3 ≤ d := by omega
    have h2d : 2 ≠ d := by omega
    have h1d2 : 1 ≠ d * 2 := by omega
    have h1d3 : 1 ≠ d * 3 := by omega
    have h2d3 : 2 ≠ d * 3 := by omega
    simp [h1, h2, hd3, h2d, h1d2, h1d3, h2d3]

theorem coeffs_qEulerProductSeries_small :
    (PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 1),
      PowerSeries.coeff (R := ℤ) 1 (qEulerProductSeries 1),
      PowerSeries.coeff (R := ℤ) 2 (qEulerProductSeries 1),
      PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 2),
      PowerSeries.coeff (R := ℤ) 1 (qEulerProductSeries 2),
      PowerSeries.coeff (R := ℤ) 2 (qEulerProductSeries 2),
      PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 3),
      PowerSeries.coeff (R := ℤ) 1 (qEulerProductSeries 3),
      PowerSeries.coeff (R := ℤ) 2 (qEulerProductSeries 3),
      PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 6),
      PowerSeries.coeff (R := ℤ) 1 (qEulerProductSeries 6),
      PowerSeries.coeff (R := ℤ) 2 (qEulerProductSeries 6)) =
      (1, -1, -1, 1, 0, -1, 1, 0, 0, 1, 0, 0) := by
  simp [coeff_zero_qEulerProductSeries, coeff_one_qEulerProductSeries,
    coeff_two_qEulerProductSeries]

private theorem coeff_nsmul (a : ℕ) (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (a • f) = a * PowerSeries.coeff (R := ℤ) n f := by
  rw [map_nsmul]
  simp [nsmul_eq_mul]

private theorem coeff_mul_zero (f g : PowerSeries ℤ) :
    PowerSeries.coeff (R := ℤ) 0 (f * g) = PowerSeries.coeff (R := ℤ) 0 f *
      PowerSeries.coeff (R := ℤ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero]
  simp

private theorem coeff_mul_one (f g : PowerSeries ℤ) :
    PowerSeries.coeff (R := ℤ) 1 (f * g) = PowerSeries.coeff (R := ℤ) 0 f *
        PowerSeries.coeff (R := ℤ) 1 g + PowerSeries.coeff (R := ℤ) 1 f *
        PowerSeries.coeff (R := ℤ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  simp [Finset.sum_range_succ]

private theorem coeff_mul_two (f g : PowerSeries ℤ) :
    PowerSeries.coeff (R := ℤ) 2 (f * g) = PowerSeries.coeff (R := ℤ) 0 f *
        PowerSeries.coeff (R := ℤ) 2 g + PowerSeries.coeff (R := ℤ) 1 f *
        PowerSeries.coeff (R := ℤ) 1 g + PowerSeries.coeff (R := ℤ) 2 f *
        PowerSeries.coeff (R := ℤ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  simp [Finset.sum_range_succ]

private theorem coeff_pow_zero (f : PowerSeries ℤ) (m : ℕ) :
    PowerSeries.coeff (R := ℤ) 0 (f ^ m) = PowerSeries.coeff (R := ℤ) 0 f ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, coeff_mul_zero, ih]
    simp [pow_succ]

private theorem coeff_pow_one (f : PowerSeries ℤ)
    (h0 : PowerSeries.coeff (R := ℤ) 0 f = 1) :
    ∀ m : ℕ, PowerSeries.coeff (R := ℤ) 1 (f ^ m) =
      m * PowerSeries.coeff (R := ℤ) 1 f := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, coeff_mul_one, coeff_pow_zero, ih]
    simp [h0]
    ring

private theorem coeff_pow_two (f : PowerSeries ℤ)
    (h0 : PowerSeries.coeff (R := ℤ) 0 f = 1) :
    ∀ m : ℕ, PowerSeries.coeff (R := ℤ) 2 (f ^ m) =
      m * PowerSeries.coeff (R := ℤ) 2 f +
        (m.choose 2 : ℤ) * PowerSeries.coeff (R := ℤ) 1 f ^ 2 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, coeff_mul_two, coeff_pow_zero, coeff_pow_one f h0 m, ih]
    simp [h0, Nat.choose_succ_succ]
    ring

private theorem coeff_sigma_subst_zero (k : ℕ) (hk : 0 < k) :
    PowerSeries.coeff (R := ℤ) 0
      (MvPowerSeries.subst (R := ℤ) (S := ℤ)
        (fun (_ : Unit) => PowerSeries.X ^ k) sigmaOneSeries) = 0 := by
  rw [coeff_subst_X_pow sigmaOneSeries hk]
  simp [sigmaOneSeries, coeff_sigmaOneSeries, ArithmeticFunction.sigma_one_apply,
    Nat.divisors]

private theorem coeff_sigma_subst_one (k : ℕ) (hk : 0 < k) :
    PowerSeries.coeff (R := ℤ) 1
      (MvPowerSeries.subst (R := ℤ) (S := ℤ)
        (fun (_ : Unit) => PowerSeries.X ^ k) sigmaOneSeries) =
      if k = 1 then 1 else 0 := by
  rw [coeff_subst_X_pow sigmaOneSeries hk]
  by_cases h : k = 1
  · subst k
    norm_num [sigmaOneSeries, coeff_sigmaOneSeries, ArithmeticFunction.sigma_one_apply,
      Nat.divisors]
    decide
  · simp [h, sigmaOneSeries, coeff_sigmaOneSeries, ArithmeticFunction.sigma_one_apply,
      Nat.divisors]

private theorem coeff_sigma_subst_two (k : ℕ) (hk : 0 < k) :
    PowerSeries.coeff (R := ℤ) 2
      (MvPowerSeries.subst (R := ℤ) (S := ℤ)
        (fun (_ : Unit) => PowerSeries.X ^ k) sigmaOneSeries) =
      if k = 1 then 3 else if k = 2 then 1 else 0 := by
  rw [coeff_subst_X_pow sigmaOneSeries hk]
  by_cases h1 : k = 1
  · subst k
    norm_num [sigmaOneSeries, coeff_sigmaOneSeries, ArithmeticFunction.sigma_one_apply,
      Nat.divisors]
    decide
  by_cases h2 : k = 2
  · subst k
    norm_num [sigmaOneSeries, coeff_sigmaOneSeries, ArithmeticFunction.sigma_one_apply,
      Nat.divisors]
    decide
  · have hknot : ¬ k ∣ 2 := by
      intro h
      have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h
      omega
    simp [h1, h2, hknot]

theorem coeff_zero_hauptmodulLogDerivativeSeries :
    PowerSeries.coeff (R := ℤ) 0 hauptmodulLogDerivativeSeries = 1 := by
  rw [hauptmodulLogDerivativeSeries]
  simp only [map_add, map_sub, map_nsmul]
  simp only [coeff_nsmul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_one]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [coeff_subst_X_pow sigmaOneSeries (by norm_num) 0,
    coeff_subst_X_pow sigmaOneSeries (by norm_num) 0,
    coeff_subst_X_pow sigmaOneSeries (by norm_num) 0]
  norm_num [sigmaOneSeries, coeff_sigmaOneSeries, ArithmeticFunction.sigma_one_apply,
    Nat.divisors]

theorem coeff_one_hauptmodulLogDerivativeSeries :
    PowerSeries.coeff (R := ℤ) 1 hauptmodulLogDerivativeSeries = -4 := by
  rw [hauptmodulLogDerivativeSeries]
  simp only [map_add, map_sub, map_nsmul]
  simp only [coeff_nsmul, PowerSeries.coeff_one]
  rw [coeff_subst_X_pow sigmaOneSeries (by norm_num) 1,
    coeff_subst_X_pow sigmaOneSeries (by norm_num) 1,
    coeff_subst_X_pow sigmaOneSeries (by norm_num) 1]
  norm_num [sigmaOneSeries, coeff_sigmaOneSeries, ArithmeticFunction.sigma_one_apply,
    Nat.divisors]
  decide

theorem coeff_two_hauptmodulLogDerivativeSeries :
    PowerSeries.coeff (R := ℤ) 2 hauptmodulLogDerivativeSeries = 4 := by
  rw [hauptmodulLogDerivativeSeries]
  simp only [map_add, map_sub, map_nsmul]
  simp only [coeff_nsmul, PowerSeries.coeff_one]
  rw [coeff_subst_X_pow sigmaOneSeries (by norm_num) 2,
    coeff_subst_X_pow sigmaOneSeries (by norm_num) 2,
    coeff_subst_X_pow sigmaOneSeries (by norm_num) 2]
  norm_num [sigmaOneSeries, coeff_sigmaOneSeries, ArithmeticFunction.sigma_one_apply,
    Nat.divisors]
  decide

/-- Formal q-product numerator of the square of the case-C eta quotient. -/
noncomputable def caseCSquareNumerator : PowerSeries ℤ :=
  qEulerProductSeries 2 ^ 12 * qEulerProductSeries 3 ^ 2

/-- Formal q-product denominator of the square of the case-C eta quotient. -/
noncomputable def caseCSquareDenominator : PowerSeries ℤ :=
  qEulerProductSeries 1 ^ 6 * qEulerProductSeries 6 ^ 4

theorem coeffs_caseCSquareNumerator :
    (PowerSeries.coeff (R := ℤ) 0 caseCSquareNumerator,
      PowerSeries.coeff (R := ℤ) 1 caseCSquareNumerator,
      PowerSeries.coeff (R := ℤ) 2 caseCSquareNumerator) = (1, 0, -12) := by
  have h20 := coeff_zero_qEulerProductSeries 2 (by norm_num)
  have h21 := coeff_one_qEulerProductSeries 2 (by norm_num)
  have h22 := coeff_two_qEulerProductSeries 2 (by norm_num)
  have h30 := coeff_zero_qEulerProductSeries 3 (by norm_num)
  have h31 := coeff_one_qEulerProductSeries 3 (by norm_num)
  have h32 := coeff_two_qEulerProductSeries 3 (by norm_num)
  norm_num at h20 h21 h22 h30 h31 h32
  have h20' : PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 2) = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h20
  have h30' : PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 3) = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h30
  apply Prod.ext
  · simp only [caseCSquareNumerator, coeff_mul_zero, coeff_pow_zero, h20, h30]
    norm_num [h20, h30, h20', h30']
  · apply Prod.ext
    · simp only [caseCSquareNumerator, coeff_mul_one, coeff_pow_zero,
        coeff_pow_one _ h20', coeff_pow_one _ h30', h20, h21, h30, h31]
      norm_num [h20, h30, h20', h30', h21, h31]
    · simp only [caseCSquareNumerator, coeff_mul_two, coeff_pow_zero,
        coeff_pow_one _ h20', coeff_pow_two _ h20', coeff_pow_zero,
        coeff_pow_one _ h30', coeff_pow_two _ h30', h20, h21, h22, h30, h31, h32]
      norm_num [Nat.choose, h20, h30, h20', h30', h21, h22, h31, h32]

theorem coeffs_caseCSquareDenominator :
    (PowerSeries.coeff (R := ℤ) 0 caseCSquareDenominator,
      PowerSeries.coeff (R := ℤ) 1 caseCSquareDenominator,
      PowerSeries.coeff (R := ℤ) 2 caseCSquareDenominator) = (1, -6, 9) := by
  have h10 := coeff_zero_qEulerProductSeries 1 (by norm_num)
  have h11 := coeff_one_qEulerProductSeries 1 (by norm_num)
  have h12 := coeff_two_qEulerProductSeries 1 (by norm_num)
  have h60 := coeff_zero_qEulerProductSeries 6 (by norm_num)
  have h61 := coeff_one_qEulerProductSeries 6 (by norm_num)
  have h62 := coeff_two_qEulerProductSeries 6 (by norm_num)
  norm_num at h10 h11 h12 h60 h61 h62
  have h10' : PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 1) = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h10
  have h60' : PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 6) = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h60
  apply Prod.ext
  · simp only [caseCSquareDenominator, coeff_mul_zero, coeff_pow_zero, h10, h60]
    norm_num [h10, h60, h10', h60']
  · apply Prod.ext
    · simp only [caseCSquareDenominator, coeff_mul_one, coeff_pow_zero,
        coeff_pow_one _ h10', coeff_pow_one _ h60', h10, h11, h60, h61]
      norm_num [h10, h60, h10', h60', h11, h61]
    · simp only [caseCSquareDenominator, coeff_mul_two, coeff_pow_zero,
        coeff_pow_one _ h10', coeff_pow_two _ h10', coeff_pow_zero,
        coeff_pow_one _ h60', coeff_pow_two _ h60', h10, h11, h12, h60, h61, h62]
      norm_num [Nat.choose, h10, h60, h10', h60', h11, h12, h61, h62]

theorem coeffs_hauptmodul_small :
    (PowerSeries.coeff (R := ℤ) 0 hauptmodul,
      PowerSeries.coeff (R := ℤ) 1 hauptmodul,
      PowerSeries.coeff (R := ℤ) 2 hauptmodul,
      PowerSeries.coeff (R := ℤ) 3 hauptmodul) = (0, 1, -4, 10) := by
  simp [constantCoeff_hauptmodul, coeff_one_hauptmodul,
    coeff_two_hauptmodul, coeff_three_hauptmodul]

/-- The polynomial factor `1 - 10H + 9H^2` in the target identity. -/
noncomputable def hauptmodulK : PowerSeries ℤ :=
  1 - 10 • hauptmodul + 9 • hauptmodul ^ 2

theorem coeffs_hauptmodulK :
    (PowerSeries.coeff (R := ℤ) 0 hauptmodulK,
      PowerSeries.coeff (R := ℤ) 1 hauptmodulK,
      PowerSeries.coeff (R := ℤ) 2 hauptmodulK) = (1, -10, 49) := by
  have h0 := coeffs_hauptmodul_small
  have h00 : PowerSeries.coeff (R := ℤ) 0 hauptmodul = 0 := congrArg Prod.fst h0
  have h01 : PowerSeries.coeff (R := ℤ) 1 hauptmodul = 1 :=
    congrArg (fun p => p.2.1) h0
  have h02 : PowerSeries.coeff (R := ℤ) 2 hauptmodul = -4 :=
    congrArg (fun p => p.2.2.1) h0
  apply Prod.ext
  · simp only [hauptmodulK, map_sub, map_add, coeff_nsmul,
      PowerSeries.coeff_one, pow_two, coeff_mul_zero, h00]
    norm_num
  · apply Prod.ext
    · simp only [hauptmodulK, map_sub, map_add, coeff_nsmul,
        pow_two, coeff_mul_one, h00, h01]
      norm_num
    · simp only [hauptmodulK, map_sub, map_add, coeff_nsmul,
        pow_two, coeff_mul_two, h00, h01, h02]
      norm_num

/-- The series `r` obtained by removing the leading `X` from the Hauptmodul. -/
noncomputable def hauptmodulShift : PowerSeries ℤ :=
  PowerSeries.mk (fun n => PowerSeries.coeff (R := ℤ) (n + 1) hauptmodul)

theorem coeffs_hauptmodulShift :
    (PowerSeries.coeff (R := ℤ) 0 hauptmodulShift,
      PowerSeries.coeff (R := ℤ) 1 hauptmodulShift,
      PowerSeries.coeff (R := ℤ) 2 hauptmodulShift) = (1, -4, 10) := by
  simp [hauptmodulShift, PowerSeries.coeff_mk, coeff_one_hauptmodul,
    coeff_two_hauptmodul, coeff_three_hauptmodul]

/-- The formal series `r + X*r'` occurring in the logarithmic derivative. -/
noncomputable def hauptmodulDerivativeNumerator : PowerSeries ℤ :=
  hauptmodulShift + PowerSeries.X * hauptmodulShift.derivativeFun

theorem coeffs_hauptmodulDerivativeNumerator :
    (PowerSeries.coeff (R := ℤ) 0 hauptmodulDerivativeNumerator,
      PowerSeries.coeff (R := ℤ) 1 hauptmodulDerivativeNumerator,
      PowerSeries.coeff (R := ℤ) 2 hauptmodulDerivativeNumerator) = (1, -8, 30) := by
  have h := coeffs_hauptmodulShift
  have h0 : PowerSeries.coeff (R := ℤ) 0 hauptmodulShift = 1 := congrArg Prod.fst h
  have h1 : PowerSeries.coeff (R := ℤ) 1 hauptmodulShift = -4 :=
    congrArg (fun p => p.2.1) h
  have h2 : PowerSeries.coeff (R := ℤ) 2 hauptmodulShift = 10 :=
    congrArg (fun p => p.2.2) h
  apply Prod.ext
  · simp only [hauptmodulDerivativeNumerator, map_add,
      PowerSeries.coeff_zero_X_mul, h0]
    norm_num
  · apply Prod.ext
    · simp only [hauptmodulDerivativeNumerator, map_add,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun, h0, h1]
      norm_num
    · simp only [hauptmodulDerivativeNumerator, map_add,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun, h1, h2]
      norm_num

/-- The cleared formal numerator for the three-coefficient comparison. -/
noncomputable def hauptmodulDerivativeClearedNumerator : PowerSeries ℤ :=
  hauptmodulDerivativeNumerator * caseCSquareDenominator -
    (hauptmodulK * caseCSquareNumerator) * hauptmodulShift

theorem coeffs_hauptmodulDerivativeClearedNumerator :
    (PowerSeries.coeff (R := ℤ) 0 hauptmodulDerivativeClearedNumerator,
      PowerSeries.coeff (R := ℤ) 1 hauptmodulDerivativeClearedNumerator,
      PowerSeries.coeff (R := ℤ) 2 hauptmodulDerivativeClearedNumerator) = (0, 0, 0) := by
  have ha := coeffs_hauptmodulDerivativeNumerator
  have ht := coeffs_caseCSquareDenominator
  have hk := coeffs_hauptmodulK
  have hs := coeffs_caseCSquareNumerator
  have hr := coeffs_hauptmodulShift
  have ha0 : PowerSeries.coeff (R := ℤ) 0 hauptmodulDerivativeNumerator = 1 :=
    congrArg Prod.fst ha
  have ha1 : PowerSeries.coeff (R := ℤ) 1 hauptmodulDerivativeNumerator = -8 :=
    congrArg (fun p => p.2.1) ha
  have ha2 : PowerSeries.coeff (R := ℤ) 2 hauptmodulDerivativeNumerator = 30 :=
    congrArg (fun p => p.2.2) ha
  have ht0 : PowerSeries.coeff (R := ℤ) 0 caseCSquareDenominator = 1 :=
    congrArg Prod.fst ht
  have ht1 : PowerSeries.coeff (R := ℤ) 1 caseCSquareDenominator = -6 :=
    congrArg (fun p => p.2.1) ht
  have ht2 : PowerSeries.coeff (R := ℤ) 2 caseCSquareDenominator = 9 :=
    congrArg (fun p => p.2.2) ht
  have hk0 : PowerSeries.coeff (R := ℤ) 0 hauptmodulK = 1 := congrArg Prod.fst hk
  have hk1 : PowerSeries.coeff (R := ℤ) 1 hauptmodulK = -10 :=
    congrArg (fun p => p.2.1) hk
  have hk2 : PowerSeries.coeff (R := ℤ) 2 hauptmodulK = 49 :=
    congrArg (fun p => p.2.2) hk
  have hs0 : PowerSeries.coeff (R := ℤ) 0 caseCSquareNumerator = 1 :=
    congrArg Prod.fst hs
  have hs1 : PowerSeries.coeff (R := ℤ) 1 caseCSquareNumerator = 0 :=
    congrArg (fun p => p.2.1) hs
  have hs2 : PowerSeries.coeff (R := ℤ) 2 caseCSquareNumerator = -12 :=
    congrArg (fun p => p.2.2) hs
  have hr0 : PowerSeries.coeff (R := ℤ) 0 hauptmodulShift = 1 := congrArg Prod.fst hr
  have hr1 : PowerSeries.coeff (R := ℤ) 1 hauptmodulShift = -4 :=
    congrArg (fun p => p.2.1) hr
  have hr2 : PowerSeries.coeff (R := ℤ) 2 hauptmodulShift = 10 :=
    congrArg (fun p => p.2.2) hr
  have hks0 : PowerSeries.coeff (R := ℤ) 0 (hauptmodulK * caseCSquareNumerator) = 1 := by
    rw [coeff_mul_zero, hk0, hs0]
    norm_num
  have hks1 : PowerSeries.coeff (R := ℤ) 1 (hauptmodulK * caseCSquareNumerator) = -10 := by
    rw [coeff_mul_one, hk0, hk1, hs0, hs1]
    norm_num
  have hks2 : PowerSeries.coeff (R := ℤ) 2 (hauptmodulK * caseCSquareNumerator) = 37 := by
    rw [coeff_mul_two, hk0, hk1, hk2, hs0, hs1, hs2]
    norm_num
  apply Prod.ext
  · simp only [hauptmodulDerivativeClearedNumerator, map_sub, coeff_mul_zero,
      coeff_mul_zero, ha0, ht0, hk0, hs0, hr0]
    norm_num
  · apply Prod.ext
    · simp only [hauptmodulDerivativeClearedNumerator, map_sub, coeff_mul_one,
        ha0, ha1, ht0, ht1, hks0, hks1, hr0, hr1]
      norm_num
    · simp only [hauptmodulDerivativeClearedNumerator, map_sub, coeff_mul_two,
        ha0, ha1, ha2, ht0, ht1, ht2, hks0, hks1, hks2,
        hr0, hr1, hr2]
      norm_num

theorem coeffs_hauptmodulDerivative_small :
    (PowerSeries.coeff (R := ℤ) 0 hauptmodul.derivativeFun,
      PowerSeries.coeff (R := ℤ) 1 hauptmodul.derivativeFun,
      PowerSeries.coeff (R := ℤ) 2 hauptmodul.derivativeFun) = (1, -8, 30) := by
  simp [PowerSeries.coeff_derivativeFun, coeff_one_hauptmodul,
    coeff_two_hauptmodul, coeff_three_hauptmodul]

end DirichletL
