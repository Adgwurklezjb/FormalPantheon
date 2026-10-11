import Analysis.PowerSeriesAnalytic

/-!
The literal B2 and B3 factorial series in CDT v2, `defB`, and their
equations in `diffformulas` (supplied TeX lines 7327-7348 and 7975-7982).
The exact coefficient bounds give convergence on the open disk of radius four.
-/

namespace DirichletL

open scoped NNReal ENNReal

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)

/-- The coefficient of degree n in the factorial quotient B3/y. -/
noncomputable def pureB3QuotientCoeff (n : ℕ) : ℚ :=
  (n.factorial : ℚ) ^ 2 / (2 * n + 2).factorial

@[simp]
theorem pureB3QuotientCoeff_zero : pureB3QuotientCoeff 0 = 1 / 2 := by
  norm_num [pureB3QuotientCoeff]

theorem pureB3QuotientCoeff_recurrence (n : ℕ) :
    2 * ((n : ℚ) + 2) * (2 * n + 3) * pureB3QuotientCoeff (n + 1) =
      ((n : ℚ) + 1) ^ 2 * pureB3QuotientCoeff n := by
  dsimp only [pureB3QuotientCoeff]
  rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 1 + 1 by omega,
    Nat.factorial_succ (2 * n + 2 + 1), Nat.factorial_succ (2 * n + 2),
    Nat.factorial_succ n]
  push_cast
  field_simp
  ring

theorem pureB3QuotientCoeff_succ (n : ℕ) :
    pureB3QuotientCoeff (n + 1) =
      (((n : ℚ) + 1) ^ 2 / (2 * (n + 2) * (2 * n + 3))) *
        pureB3QuotientCoeff n := by
  apply mul_left_cancel₀ (by positivity : (2 : ℚ) * (n + 2) * (2 * n + 3) ≠ 0)
  rw [pureB3QuotientCoeff_recurrence, ← mul_assoc,
    mul_div_cancel₀ _ (by positivity)]

theorem pureB3QuotientCoeff_nonneg (n : ℕ) : 0 ≤ pureB3QuotientCoeff n := by
  unfold pureB3QuotientCoeff
  positivity

theorem pureB3QuotientCoeff_le_quarter (n : ℕ) :
    pureB3QuotientCoeff (n + 1) ≤ (1 / 4 : ℚ) * pureB3QuotientCoeff n := by
  rw [pureB3QuotientCoeff_succ]
  apply mul_le_mul_of_nonneg_right _ (pureB3QuotientCoeff_nonneg n)
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℚ) n]

theorem pureB3QuotientCoeff_le (n : ℕ) : pureB3QuotientCoeff n ≤ (1 / 4 : ℚ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      _ ≤ (1 / 4 : ℚ) * pureB3QuotientCoeff n := pureB3QuotientCoeff_le_quarter n
      _ ≤ (1 / 4 : ℚ) * (1 / 4 : ℚ) ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- The literal factorial B3 series, with no degree-zero term. -/
noncomputable def pureB3Series : PowerSeries ℚ := x * PowerSeries.mk pureB3QuotientCoeff

@[simp]
theorem constantCoeff_pureB3Series : PowerSeries.constantCoeff (R := ℚ) pureB3Series = 0 := by
  simp [pureB3Series]

@[simp]
theorem coeff_pureB3Series_succ (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 1) pureB3Series = pureB3QuotientCoeff n := by
  rw [pureB3Series, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]

/-- The second-order equation of B3 obtained from its factorial recurrence. -/
noncomputable def pureB3Operator (f : PowerSeries ℚ) : PowerSeries ℚ :=
  x * (4 - x) * D (D f) + (2 - x) * D f

private theorem pureB3Operator_expanded (f : PowerSeries ℚ) :
    pureB3Operator f = PowerSeries.C (R := ℚ) 4 * (x * D (D f)) +
      PowerSeries.C (R := ℚ) 2 * D f - x * D (x * D f) := by
  simp only [pureB3Operator, map_ofNat, Derivation.leibniz,
    PowerSeries.derivative_X, smul_eq_mul]
  ring

private theorem coeff_X_mul_derivative (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (x * D f) = (n : ℚ) * PowerSeries.coeff (R := ℚ) n f := by
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    push_cast
    ring

theorem coeff_pureB3Operator (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (pureB3Operator f) =
      2 * ((n : ℚ) + 1) * (2 * n + 1) * PowerSeries.coeff (R := ℚ) (n + 1) f -
        (n : ℚ) ^ 2 * PowerSeries.coeff (R := ℚ) n f := by
  simp only [pureB3Operator_expanded, map_sub, map_add, PowerSeries.coeff_C_mul,
    coeff_X_mul_derivative, PowerSeries.coeff_derivative]
  ring

theorem pureB3Series_ode : pureB3Operator pureB3Series = 1 := by
  ext n
  cases n with
  | zero => norm_num [coeff_pureB3Operator]
  | succ n =>
    rw [coeff_pureB3Operator, coeff_pureB3Series_succ, coeff_pureB3Series_succ]
    simp only [PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n)]
    push_cast
    have h := pureB3QuotientCoeff_recurrence n
    linear_combination h

theorem le_radius_complexSeries_pureB3Series : 4 ≤ (complexSeries pureB3Series).radius := by
  apply (complexSeries pureB3Series).le_radius_of_bound (r := (4 : ℝ≥0)) 4
  intro n
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    NNReal.coe_ofNat]
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_pureB3Series_succ, Complex.norm_ratCast]
    have hb : (pureB3QuotientCoeff n : ℝ) ≤ (1 / 4 : ℝ) ^ n := by
      simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr (pureB3QuotientCoeff_le n)
    rw [abs_of_nonneg ((Rat.cast_nonneg (K := ℝ)).mpr (pureB3QuotientCoeff_nonneg n))]
    calc
      _ ≤ (1 / 4 : ℝ) ^ n * 4 ^ (n + 1) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 4 := by rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num

/-- The B2 series determined by the exact B3 differential identity in `diffformulas`. -/
noncomputable def pureB2Series : PowerSeries ℚ :=
  x * (PowerSeries.C (R := ℚ) 2 - (PowerSeries.C (R := ℚ) 4 - x) * D pureB3Series)

@[simp]
theorem constantCoeff_pureB2Series : PowerSeries.constantCoeff (R := ℚ) pureB2Series = 0 := by
  simp [pureB2Series]

@[simp]
theorem coeff_one_pureB2Series : PowerSeries.coeff (R := ℚ) 1 pureB2Series = 0 := by
  rw [show 1 = 0 + 1 by rfl, pureB2Series, PowerSeries.coeff_succ_X_mul]
  simp only [sub_mul, map_sub, PowerSeries.coeff_C, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative, coeff_pureB3Series_succ]
  norm_num

private theorem coeff_pureB2Series_add_two_expanded (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 2) pureB2Series =
      -4 * ((n : ℚ) + 2) * pureB3QuotientCoeff (n + 1) +
        ((n : ℚ) + 1) * pureB3QuotientCoeff n := by
  rw [show n + 2 = (n + 1) + 1 by omega, pureB2Series, PowerSeries.coeff_succ_X_mul]
  simp only [sub_mul, map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n),
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
    coeff_pureB3Series_succ]
  push_cast
  ring

theorem coeff_pureB2Series_add_two_ratio (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 2) pureB2Series =
      (((n : ℚ) + 1) / (2 * n + 3)) * pureB3QuotientCoeff n := by
  rw [coeff_pureB2Series_add_two_expanded, pureB3QuotientCoeff_succ]
  field_simp
  ring

/-- The literal factorial coefficient in `defB`, with the initial index shifted by two. -/
theorem coeff_pureB2Series_add_two (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 2) pureB2Series =
      2 * (n.factorial : ℚ) * (n + 2).factorial / (2 * n + 4).factorial := by
  rw [coeff_pureB2Series_add_two_ratio, pureB3QuotientCoeff,
    show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ (n + 1), Nat.factorial_succ n,
    show 2 * n + 4 = (2 * n + 2) + 1 + 1 by omega,
    Nat.factorial_succ (2 * n + 2 + 1), Nat.factorial_succ (2 * n + 2)]
  push_cast
  field_simp
  ring

theorem coeff_pureB2Series_add_two_nonneg (n : ℕ) :
    0 ≤ PowerSeries.coeff (R := ℚ) (n + 2) pureB2Series := by
  rw [coeff_pureB2Series_add_two_ratio]
  exact mul_nonneg (by positivity) (pureB3QuotientCoeff_nonneg n)

theorem coeff_pureB2Series_add_two_le (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 2) pureB2Series ≤ pureB3QuotientCoeff n := by
  rw [coeff_pureB2Series_add_two_ratio]
  apply mul_le_of_le_one_left (pureB3QuotientCoeff_nonneg n)
  apply (div_le_one (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℚ) n]

theorem le_radius_complexSeries_pureB2Series : 4 ≤ (complexSeries pureB2Series).radius := by
  apply (complexSeries pureB2Series).le_radius_of_bound (r := (4 : ℝ≥0)) 16
  intro n
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    NNReal.coe_ofNat]
  rcases n with _ | (_ | n)
  · simp
  · simp
  · rw [Complex.norm_ratCast]
    have hn : 0 ≤ (PowerSeries.coeff (R := ℚ) (n + 2) pureB2Series : ℝ) :=
      (Rat.cast_nonneg (K := ℝ)).mpr (coeff_pureB2Series_add_two_nonneg n)
    have hb : (PowerSeries.coeff (R := ℚ) (n + 2) pureB2Series : ℝ) ≤ (1 / 4 : ℝ) ^ n := by
      simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr
          ((coeff_pureB2Series_add_two_le n).trans (pureB3QuotientCoeff_le n))
    rw [abs_of_nonneg hn]
    calc
      _ ≤ (1 / 4 : ℝ) ^ n * 4 ^ (n + 2) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 16 := by rw [pow_add, ← mul_assoc, ← mul_pow]; norm_num

theorem pureB2Series_ode :
    x * (4 - x) * D pureB2Series = (2 - x) * pureB2Series + x ^ 2 := by
  have h2 : D (2 : PowerSeries ℚ) = 0 := (PowerSeries.derivative ℚ).map_natCast 2
  have h4 : D (4 : PowerSeries ℚ) = 0 := (PowerSeries.derivative ℚ).map_natCast 4
  have h := pureB3Series_ode
  simp only [pureB3Operator] at h
  simp only [pureB2Series, map_ofNat, Derivation.leibniz, map_sub, h2, h4,
    PowerSeries.derivative_X, smul_eq_mul]
  linear_combination -x * (4 - x) * h

end DirichletL
