import Analysis.GeneratingFunctions

/-!
Coefficientwise formal integral and quotient-by-`X` operations.

These operations provide the algebraic power-series layer for the first three
functions in CDT v2, Lemma `14functions`. They make no claim
about analytic integration or convergence.
-/

namespace DirichletL

/-- The formal antiderivative with zero constant coefficient. -/
noncomputable def formalIntegral (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0
    else PowerSeries.coeff (R := ℚ) (n - 1) f / (n : ℚ))

@[simp]
theorem coeff_formalIntegral (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (formalIntegral f) =
      if n = 0 then 0 else PowerSeries.coeff (R := ℚ) (n - 1) f / (n : ℚ) := by
  simp [formalIntegral]

theorem coeff_formalIntegral_succ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (n + 1) (formalIntegral f) =
      PowerSeries.coeff (R := ℚ) n f / (n + 1 : ℚ) := by
  simp [coeff_formalIntegral]

theorem derivative_formalIntegral (f : PowerSeries ℚ) :
    (formalIntegral f).derivativeFun = f := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_derivativeFun, coeff_formalIntegral]
  rw [if_neg (Nat.succ_ne_zero n)]
  rw [Nat.add_sub_cancel]
  push_cast
  field_simp

@[simp]
theorem constantCoeff_formalIntegral (f : PowerSeries ℚ) :
    PowerSeries.constantCoeff (R := ℚ) (formalIntegral f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_formalIntegral]
  simp

/-- The coefficient shift that removes one factor of `X`. -/
noncomputable def formalShift (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => PowerSeries.coeff (R := ℚ) (n + 1) f)

@[simp]
theorem coeff_formalShift (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (formalShift f) = PowerSeries.coeff (R := ℚ) (n + 1) f := by
  simp [formalShift]

theorem formalShift_mul_X (f : PowerSeries ℚ) :
    formalShift f * PowerSeries.X =
      f - PowerSeries.C (R := ℚ) (PowerSeries.constantCoeff (R := ℚ) f) := by
  rw [PowerSeries.sub_const_eq_shift_mul_X]
  rfl

theorem X_mul_formalShift (f : PowerSeries ℚ) :
    PowerSeries.X * formalShift f =
      f - PowerSeries.C (R := ℚ) (PowerSeries.constantCoeff (R := ℚ) f) := by
  rw [PowerSeries.sub_const_eq_X_mul_shift]
  rfl

theorem X_mul_formalShift_of_constantCoeff_zero {f : PowerSeries ℚ}
    (hf : PowerSeries.constantCoeff (R := ℚ) f = 0) :
    PowerSeries.X * formalShift f = f := by
  rw [X_mul_formalShift, hf]
  simp

/-- Remove the constant and linear terms before a second coefficient shift. -/
noncomputable def formalSecondShift (f : PowerSeries ℚ) : PowerSeries ℚ :=
  formalShift (formalShift f - PowerSeries.C (R := ℚ) (PowerSeries.coeff (R := ℚ) 1 f))

@[simp]
theorem coeff_formalSecondShift (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (formalSecondShift f) = PowerSeries.coeff (R := ℚ) (n + 2) f := by
  simp [formalSecondShift, coeff_formalShift, PowerSeries.coeff_C, Nat.add_assoc]

theorem formalSecondShift_eq (f : PowerSeries ℚ) :
    formalSecondShift f = formalShift (formalShift f) := by
  ext n
  simp [Nat.add_assoc]

theorem constantCoeff_formalShift_sub_linear (f : PowerSeries ℚ) :
    PowerSeries.constantCoeff (R := ℚ)
      (formalShift f - PowerSeries.C (R := ℚ) (PowerSeries.coeff (R := ℚ) 1 f)) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub,
    coeff_formalShift, PowerSeries.coeff_C]
  simp

theorem X_sq_mul_formalSecondShift (f : PowerSeries ℚ) :
    PowerSeries.X ^ 2 * formalSecondShift f =
      f - PowerSeries.C (R := ℚ) (PowerSeries.constantCoeff (R := ℚ) f) -
        PowerSeries.X * PowerSeries.C (R := ℚ) (PowerSeries.coeff (R := ℚ) 1 f) := by
  have hzero := constantCoeff_formalShift_sub_linear f
  have hfirst := X_mul_formalShift_of_constantCoeff_zero hzero
  have hbase := X_mul_formalShift f
  dsimp [formalSecondShift]
  rw [pow_two, mul_assoc, hfirst, mul_sub, hbase]

end DirichletL
