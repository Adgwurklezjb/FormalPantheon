import Analysis.ZagierDerivativeCoefficients
import Arithmetic.PowerSeriesEuler

/-!
Exact denominator-cleared q-series data for Zagier (2009), Section 5,
equation (7), case C. The mathematical preparation is in
-/

namespace DirichletL

/-! The integral q-series used by the analytic numerator and denominator. -/

/-- The integral numerator of the case-C eta square. -/
noncomputable def zagierCaseCN : PowerSeries ℤ := caseCSquareNumerator

/-- The integral denominator of the case-C eta square, with constant coefficient one. -/
noncomputable def zagierCaseCD : PowerSeries ℤ := caseCSquareDenominator

/-- The integral Hauptmodul in CDT's case-C normalization. -/
noncomputable def zagierHauptmodul : PowerSeries ℤ := hauptmodul

/-- Euler differentiation of an integral q-series. -/
noncomputable def zagierTheta (p : PowerSeries ℤ) : PowerSeries ℤ :=
  powerSeriesEuler ℤ p

/-- The numerator of the first Euler derivative of N/D, with denominator D squared. -/
noncomputable def zagierClearA : PowerSeries ℤ :=
  zagierTheta zagierCaseCN * zagierCaseCD -
    zagierCaseCN * zagierTheta zagierCaseCD

/-- The numerator of the second Euler derivative of N/D, with denominator D cubed. -/
noncomputable def zagierClearB : PowerSeries ℤ :=
  zagierTheta zagierClearA * zagierCaseCD -
    2 * zagierClearA * zagierTheta zagierCaseCD

/-- The polynomial factor in the second case-C differential identity. -/
noncomputable def zagierClearPolynomial : PowerSeries ℤ :=
  4 * zagierHauptmodul *
      (1 - 10 * zagierHauptmodul + 9 * zagierHauptmodul ^ 2) *
      (9 * zagierHauptmodul - 3)

/-- The second case-C difference after clearing its denominator N squared times D squared. -/
noncomputable def zagierSecondClearedSeries : PowerSeries ℤ :=
  3 * zagierClearA ^ 2 - 2 * zagierCaseCN * zagierClearB -
    zagierClearPolynomial * zagierCaseCN ^ 4

private theorem coeff_qEulerProductSeries (d n : ℕ) :
    PowerSeries.coeff (R := ℤ) n (qEulerProductSeries d) =
      PowerSeries.coeff (R := ℤ) n
        (∏ i ∈ Finset.range (n + 1), (1 - PowerSeries.X ^ (d * (i + 1)))) := by
  simp only [qEulerProductSeries, coeff_formalProduct, formalProductCoeff]

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

private theorem coeff_mul_three (f g : PowerSeries ℤ) :
    PowerSeries.coeff (R := ℤ) 3 (f * g) = PowerSeries.coeff (R := ℤ) 0 f *
        PowerSeries.coeff (R := ℤ) 3 g + PowerSeries.coeff (R := ℤ) 1 f *
        PowerSeries.coeff (R := ℤ) 2 g + PowerSeries.coeff (R := ℤ) 2 f *
        PowerSeries.coeff (R := ℤ) 1 g + PowerSeries.coeff (R := ℤ) 3 f *
        PowerSeries.coeff (R := ℤ) 0 g := by
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map, Finset.sum_map]
  simp [Finset.sum_range_succ]

private theorem coeff_mul_four (f g : PowerSeries ℤ) :
    PowerSeries.coeff (R := ℤ) 4 (f * g) = PowerSeries.coeff (R := ℤ) 0 f *
        PowerSeries.coeff (R := ℤ) 4 g + PowerSeries.coeff (R := ℤ) 1 f *
        PowerSeries.coeff (R := ℤ) 3 g + PowerSeries.coeff (R := ℤ) 2 f *
        PowerSeries.coeff (R := ℤ) 2 g + PowerSeries.coeff (R := ℤ) 3 f *
        PowerSeries.coeff (R := ℤ) 1 g + PowerSeries.coeff (R := ℤ) 4 f *
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

private theorem coeff_pow_three (f : PowerSeries ℤ)
    (h0 : PowerSeries.coeff (R := ℤ) 0 f = 1) :
    ∀ m : ℕ, PowerSeries.coeff (R := ℤ) 3 (f ^ m) =
      m * PowerSeries.coeff (R := ℤ) 3 f +
        2 * (m.choose 2 : ℤ) * PowerSeries.coeff (R := ℤ) 1 f * PowerSeries.coeff (R := ℤ) 2 f +
        (m.choose 3 : ℤ) * PowerSeries.coeff (R := ℤ) 1 f ^ 3 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, coeff_mul_three, coeff_pow_zero, coeff_pow_one f h0 m,
      coeff_pow_two f h0 m, ih]
    simp [h0, Nat.choose_succ_succ]
    ring

private theorem coeff_pow_four (f : PowerSeries ℤ)
    (h0 : PowerSeries.coeff (R := ℤ) 0 f = 1) :
    ∀ m : ℕ, PowerSeries.coeff (R := ℤ) 4 (f ^ m) =
      m * PowerSeries.coeff (R := ℤ) 4 f +
        2 * (m.choose 2 : ℤ) * PowerSeries.coeff (R := ℤ) 1 f * PowerSeries.coeff (R := ℤ) 3 f +
        (m.choose 2 : ℤ) * PowerSeries.coeff (R := ℤ) 2 f ^ 2 +
        3 * (m.choose 3 : ℤ) * PowerSeries.coeff (R := ℤ) 1 f ^ 2 * PowerSeries.coeff (R := ℤ) 2 f +
        (m.choose 4 : ℤ) * PowerSeries.coeff (R := ℤ) 1 f ^ 4 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, coeff_mul_four, coeff_pow_zero, coeff_pow_one f h0 m,
      coeff_pow_two f h0 m, coeff_pow_three f h0 m, ih]
    simp [h0, Nat.choose_succ_succ]
    ring

set_option maxHeartbeats 1000000 in
private theorem coeffs_qEulerProductSeries_caseC :
    (PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 1),
      PowerSeries.coeff (R := ℤ) 1 (qEulerProductSeries 1),
      PowerSeries.coeff (R := ℤ) 2 (qEulerProductSeries 1),
      PowerSeries.coeff (R := ℤ) 3 (qEulerProductSeries 1),
      PowerSeries.coeff (R := ℤ) 4 (qEulerProductSeries 1),
      PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 2),
      PowerSeries.coeff (R := ℤ) 1 (qEulerProductSeries 2),
      PowerSeries.coeff (R := ℤ) 2 (qEulerProductSeries 2),
      PowerSeries.coeff (R := ℤ) 3 (qEulerProductSeries 2),
      PowerSeries.coeff (R := ℤ) 4 (qEulerProductSeries 2),
      PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 3),
      PowerSeries.coeff (R := ℤ) 1 (qEulerProductSeries 3),
      PowerSeries.coeff (R := ℤ) 2 (qEulerProductSeries 3),
      PowerSeries.coeff (R := ℤ) 3 (qEulerProductSeries 3),
      PowerSeries.coeff (R := ℤ) 4 (qEulerProductSeries 3),
      PowerSeries.coeff (R := ℤ) 0 (qEulerProductSeries 6),
      PowerSeries.coeff (R := ℤ) 1 (qEulerProductSeries 6),
      PowerSeries.coeff (R := ℤ) 2 (qEulerProductSeries 6),
      PowerSeries.coeff (R := ℤ) 3 (qEulerProductSeries 6),
      PowerSeries.coeff (R := ℤ) 4 (qEulerProductSeries 6)) =
      (1, -1, -1, 0, 0, 1, 0, -1, 0, -1, 1, 0, 0, -1, 0, 1, 0, 0, 0, 0) := by
  repeat' rw [coeff_qEulerProductSeries]
  norm_num [Finset.prod_range_succ, PowerSeries.coeff_mul,
    PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
    Finset.Nat.antidiagonal_eq_map, Finset.sum_map, Finset.sum_range_succ]

theorem coeffs_zagierCaseCN :
    (PowerSeries.coeff (R := ℤ) 0 zagierCaseCN,
      PowerSeries.coeff (R := ℤ) 1 zagierCaseCN,
      PowerSeries.coeff (R := ℤ) 2 zagierCaseCN,
      PowerSeries.coeff (R := ℤ) 3 zagierCaseCN,
      PowerSeries.coeff (R := ℤ) 4 zagierCaseCN) =
      (1, 0, -12, -2, 54) := by
  have h := coeffs_qEulerProductSeries_caseC
  simp only [Prod.mk.injEq] at h
  obtain ⟨_, _, _, _, _, h20, h21, h22, h23, h24, h30, h31, h32, h33, h34,
    _, _, _, _, _⟩ := h
  simp only [zagierCaseCN, caseCSquareNumerator, coeff_mul_zero, coeff_mul_one,
    coeff_mul_two, coeff_mul_three, coeff_mul_four, coeff_pow_zero,
    coeff_pow_one _ h20, coeff_pow_two _ h20, coeff_pow_three _ h20,
    coeff_pow_four _ h20, coeff_pow_one _ h30, coeff_pow_two _ h30,
    coeff_pow_three _ h30, coeff_pow_four _ h30,
    h20, h21, h22, h23, h24, h30, h31, h32, h33, h34]
  norm_num [Nat.choose]

theorem coeffs_zagierCaseCD :
    (PowerSeries.coeff (R := ℤ) 0 zagierCaseCD,
      PowerSeries.coeff (R := ℤ) 1 zagierCaseCD,
      PowerSeries.coeff (R := ℤ) 2 zagierCaseCD,
      PowerSeries.coeff (R := ℤ) 3 zagierCaseCD,
      PowerSeries.coeff (R := ℤ) 4 zagierCaseCD) =
      (1, -6, 9, 10, -30) := by
  have h := coeffs_qEulerProductSeries_caseC
  simp only [Prod.mk.injEq] at h
  obtain ⟨h10, h11, h12, h13, h14, _, _, _, _, _, _, _, _, _, _,
    h60, h61, h62, h63, h64⟩ := h
  simp only [zagierCaseCD, caseCSquareDenominator, coeff_mul_zero, coeff_mul_one,
    coeff_mul_two, coeff_mul_three, coeff_mul_four, coeff_pow_zero,
    coeff_pow_one _ h10, coeff_pow_two _ h10, coeff_pow_three _ h10,
    coeff_pow_four _ h10, coeff_pow_one _ h60, coeff_pow_two _ h60,
    coeff_pow_three _ h60, coeff_pow_four _ h60,
    h10, h11, h12, h13, h14, h60, h61, h62, h63, h64]
  norm_num [Nat.choose]

theorem coeffs_zagierHauptmodul :
    (PowerSeries.coeff (R := ℤ) 0 zagierHauptmodul,
      PowerSeries.coeff (R := ℤ) 1 zagierHauptmodul,
      PowerSeries.coeff (R := ℤ) 2 zagierHauptmodul,
      PowerSeries.coeff (R := ℤ) 3 zagierHauptmodul,
      PowerSeries.coeff (R := ℤ) 4 zagierHauptmodul) =
      (0, 1, -4, 10, -20) := by
  have h := coeffs_qEulerProductSeries_caseC
  simp only [Prod.mk.injEq] at h
  obtain ⟨h10, h11, h12, h13, h14, h20, h21, h22, h23, h24,
    h30, h31, h32, h33, h34, h60, h61, h62, h63, h64⟩ := h
  have ht := coeffs_hauptmodul_small
  simp only [Prod.mk.injEq] at ht
  obtain ⟨ht0, ht1, ht2, ht3⟩ := ht
  have he := congrArg (PowerSeries.coeff (R := ℤ) 4) hauptmodul_mul_qEulerProductSeries
  simp only [coeff_mul_four, coeff_mul_three, coeff_mul_two, coeff_mul_one,
    coeff_mul_zero, coeff_pow_zero, coeff_pow_one _ h10, coeff_pow_two _ h10,
    coeff_pow_three _ h10, coeff_pow_four _ h10, coeff_pow_one _ h20,
    coeff_pow_two _ h20, coeff_pow_three _ h20, coeff_pow_four _ h20,
    coeff_pow_one _ h30, coeff_pow_two _ h30, coeff_pow_three _ h30,
    coeff_pow_four _ h30, coeff_pow_one _ h60, coeff_pow_two _ h60,
    coeff_pow_three _ h60, coeff_pow_four _ h60,
    h10, h11, h12, h13, h14, h20, h21, h22, h23, h24,
    h30, h31, h32, h33, h34, h60, h61, h62, h63, h64,
    ht0, ht1, ht2, ht3, PowerSeries.coeff_X] at he
  norm_num [Nat.choose] at he
  simp only [zagierHauptmodul, ht0, ht1, ht2, ht3, Prod.mk.injEq, true_and]
  linarith

theorem coeffs_zagierSecondClearedSeries :
    (PowerSeries.coeff (R := ℤ) 0 zagierSecondClearedSeries,
      PowerSeries.coeff (R := ℤ) 1 zagierSecondClearedSeries,
      PowerSeries.coeff (R := ℤ) 2 zagierSecondClearedSeries,
      PowerSeries.coeff (R := ℤ) 3 zagierSecondClearedSeries,
      PowerSeries.coeff (R := ℤ) 4 zagierSecondClearedSeries) =
      (0, 0, 0, 0, 0) := by
  have hn := coeffs_zagierCaseCN
  have hd := coeffs_zagierCaseCD
  have ht := coeffs_zagierHauptmodul
  simp only [Prod.mk.injEq] at hn hd ht
  obtain ⟨hn0, hn1, hn2, hn3, hn4⟩ := hn
  obtain ⟨hd0, hd1, hd2, hd3, hd4⟩ := hd
  obtain ⟨ht0, ht1, ht2, ht3, ht4⟩ := ht
  simp only [zagierSecondClearedSeries, zagierClearB, zagierClearA,
    zagierClearPolynomial, zagierTheta, map_sub, map_add, pow_two,
    coeff_mul_four, coeff_mul_three, coeff_mul_two, coeff_mul_one,
    coeff_mul_zero, coeff_pow_zero, coeff_pow_one _ hn0,
    coeff_pow_two _ hn0, coeff_pow_three _ hn0, coeff_pow_four _ hn0,
    coeff_powerSeriesEuler, hn0, hn1, hn2, hn3, hn4,
    hd0, hd1, hd2, hd3, hd4, ht0, ht1, ht2, ht3, ht4]
  simp only [← map_ofNat (PowerSeries.C (R := ℤ)), PowerSeries.coeff_C]
  norm_num [PowerSeries.coeff_one]

theorem coeff_zero_zagierSecondClearedSeries (m : ℕ) (hm : m < 5) :
    PowerSeries.coeff (R := ℤ) m zagierSecondClearedSeries = 0 := by
  have h := coeffs_zagierSecondClearedSeries
  simp only [Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  interval_cases m <;> assumption

end DirichletL
