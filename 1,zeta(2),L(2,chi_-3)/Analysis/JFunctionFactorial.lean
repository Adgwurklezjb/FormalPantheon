import Analysis.PowerSeriesAnalytic

/-!
The literal factorial series B5 from CDT v2, `defB5` (supplied TeX
lines 7358-7362). The quotient B5/y has a rational coefficient
recurrence and a kernel-checked radius lower bound of four.
-/

namespace DirichletL

open scoped NNReal ENNReal

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)

/-- The factorial coefficient of degree n in the quotient B5/y. -/
noncomputable def pureB5QuotientCoeff (n : ℕ) : ℚ :=
  (n.factorial : ℚ) ^ 2 / ((2 * n + 1).factorial * (2 * (n : ℚ) + 1))

@[simp]
theorem pureB5QuotientCoeff_zero : pureB5QuotientCoeff 0 = 1 := by
  norm_num [pureB5QuotientCoeff]

theorem pureB5QuotientCoeff_recurrence (n : ℕ) :
    2 * (2 * (n : ℚ) + 3) ^ 2 * pureB5QuotientCoeff (n + 1) =
      ((n : ℚ) + 1) * (2 * n + 1) * pureB5QuotientCoeff n := by
  dsimp only [pureB5QuotientCoeff]
  rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by omega,
    Nat.factorial_succ (2 * n + 1 + 1), Nat.factorial_succ (2 * n + 1),
    Nat.factorial_succ n]
  push_cast
  field_simp
  ring

theorem pureB5QuotientCoeff_succ (n : ℕ) :
    pureB5QuotientCoeff (n + 1) =
      (((n : ℚ) + 1) * (2 * n + 1) / (2 * (2 * n + 3) ^ 2)) *
        pureB5QuotientCoeff n := by
  apply mul_left_cancel₀ (by positivity : (2 : ℚ) * (2 * n + 3) ^ 2 ≠ 0)
  rw [pureB5QuotientCoeff_recurrence, ← mul_assoc,
    mul_div_cancel₀ _ (by positivity)]

theorem pureB5QuotientCoeff_nonneg (n : ℕ) : 0 ≤ pureB5QuotientCoeff n := by
  unfold pureB5QuotientCoeff
  positivity

theorem pureB5QuotientCoeff_le_quarter (n : ℕ) :
    pureB5QuotientCoeff (n + 1) ≤ (1 / 4 : ℚ) * pureB5QuotientCoeff n := by
  rw [pureB5QuotientCoeff_succ]
  apply mul_le_mul_of_nonneg_right _ (pureB5QuotientCoeff_nonneg n)
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℚ) n]

theorem pureB5QuotientCoeff_le (n : ℕ) : pureB5QuotientCoeff n ≤ (1 / 4 : ℚ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    calc
      _ ≤ (1 / 4 : ℚ) * pureB5QuotientCoeff n := pureB5QuotientCoeff_le_quarter n
      _ ≤ (1 / 4 : ℚ) * (1 / 4 : ℚ) ^ n := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- The rational factorial series P=B5/y, with constant coefficient one. -/
noncomputable def pureB5QuotientSeries : PowerSeries ℚ :=
  PowerSeries.mk pureB5QuotientCoeff

@[simp]
theorem coeff_pureB5QuotientSeries (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n pureB5QuotientSeries = pureB5QuotientCoeff n :=
  PowerSeries.coeff_mk _ _

/-- The exact B5 series of `defB5`, indexed from degree one. -/
noncomputable def pureB5Series : PowerSeries ℚ := x * pureB5QuotientSeries

@[simp]
theorem constantCoeff_pureB5Series : PowerSeries.constantCoeff (R := ℚ) pureB5Series = 0 := by
  simp [pureB5Series]

theorem coeff_pureB5Series_succ (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 1) pureB5Series =
      (n.factorial : ℚ) ^ 2 / ((2 * n + 1).factorial * (2 * (n : ℚ) + 1)) := by
  rw [pureB5Series, PowerSeries.coeff_succ_X_mul, coeff_pureB5QuotientSeries]
  rfl

/-- The second-order equation of the factorial quotient P. -/
noncomputable def pureB5QuotientOperator (f : PowerSeries ℚ) : PowerSeries ℚ :=
  2 * x ^ 2 * (4 - x) * D (D f) + x * (16 - 5 * x) * D f + (2 - x) * f

private theorem pureB5QuotientOperator_expanded (f : PowerSeries ℚ) :
    pureB5QuotientOperator f =
      PowerSeries.C (R := ℚ) 2 * (PowerSeries.C (R := ℚ) 4 * (x * D (x * D f)) +
        PowerSeries.C (R := ℚ) 4 * (x * D f) + f) -
      x * (PowerSeries.C (R := ℚ) 2 * (x * D (x * D f)) +
        PowerSeries.C (R := ℚ) 3 * (x * D f) + f) := by
  simp only [pureB5QuotientOperator, map_ofNat, Derivation.leibniz,
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

theorem coeff_pureB5QuotientOperator_zero (f : PowerSeries ℚ) :
    PowerSeries.coeff (R := ℚ) 0 (pureB5QuotientOperator f) =
      2 * PowerSeries.coeff (R := ℚ) 0 f := by
  simp only [pureB5QuotientOperator_expanded, map_sub, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_zero_X_mul, mul_zero, zero_add, sub_zero]

theorem coeff_pureB5QuotientOperator_succ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 1) (pureB5QuotientOperator f) =
      2 * (2 * (n : ℚ) + 3) ^ 2 * PowerSeries.coeff (R := ℚ) (n + 1) f -
        ((n : ℚ) + 1) * (2 * n + 1) * PowerSeries.coeff (R := ℚ) n f := by
  simp only [pureB5QuotientOperator_expanded, map_sub, map_add,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, coeff_X_mul_derivative,
    PowerSeries.coeff_derivative]
  ring

theorem pureB5QuotientSeries_ode :
    pureB5QuotientOperator pureB5QuotientSeries = 2 := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) 2]
  ext n
  cases n with
  | zero => norm_num [coeff_pureB5QuotientOperator_zero]
  | succ n =>
    rw [coeff_pureB5QuotientOperator_succ]
    simp only [coeff_pureB5QuotientSeries, pureB5QuotientCoeff_recurrence, sub_self]
    norm_num

theorem le_radius_complexSeries_pureB5QuotientSeries :
    4 ≤ (complexSeries pureB5QuotientSeries).radius := by
  apply (complexSeries pureB5QuotientSeries).le_radius_of_bound (r := (4 : ℝ≥0)) 1
  intro n
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    coeff_pureB5QuotientSeries, Complex.norm_ratCast, NNReal.coe_ofNat]
  have hb : (pureB5QuotientCoeff n : ℝ) ≤ (1 / 4 : ℝ) ^ n := by
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (pureB5QuotientCoeff_le n)
  rw [abs_of_nonneg (by exact_mod_cast pureB5QuotientCoeff_nonneg n)]
  calc
    _ ≤ (1 / 4 : ℝ) ^ n * 4 ^ n := mul_le_mul_of_nonneg_right hb (by positivity)
    _ = 1 := by rw [← mul_pow]; norm_num

theorem le_radius_complexSeries_pureB5Series : 4 ≤ (complexSeries pureB5Series).radius := by
  apply (complexSeries pureB5Series).le_radius_of_bound (r := (4 : ℝ≥0)) 4
  intro n
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_complexSeries,
    NNReal.coe_ofNat]
  cases n with
  | zero => simp
  | succ n =>
    simp only [pureB5Series, PowerSeries.coeff_succ_X_mul, coeff_pureB5QuotientSeries,
      Complex.norm_ratCast]
    have hb : (pureB5QuotientCoeff n : ℝ) ≤ (1 / 4 : ℝ) ^ n := by
      simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr (pureB5QuotientCoeff_le n)
    rw [abs_of_nonneg ((Rat.cast_nonneg (K := ℝ)).mpr (pureB5QuotientCoeff_nonneg n))]
    calc
      _ ≤ (1 / 4 : ℝ) ^ n * 4 ^ (n + 1) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = 4 := by rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num

end DirichletL
