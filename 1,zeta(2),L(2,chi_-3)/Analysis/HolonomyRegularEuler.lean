import Analysis.HolonomyFamily
import Analysis.ZagierForcedDescent

/-!
A polynomially cleared Euler system for the actual fourteen series of CDT v2,
`14functions` and `typesA` (supplied TeX 8280-8331). It uses `diffformulas`
The common denominator has nonzero constant coefficient. A quantitative
zero estimate and the transfer of polynomial degree bounds remain separate.
-/

noncomputable section

namespace DirichletL

open Polynomial
open scoped Matrix

/-- The leading fourth-order coefficient after removing its third power of X. -/
def zagierEulerDenominator : ℚ[X] :=
  (X - 4) ^ 2 * (1 + 72 * X) * (-1 + 118 * X - 122 * X ^ 2 + 144 * X ^ 3)

/-- The second and third derivative coefficients after removing X and X squared. -/
def zagierEulerDerivativeCoefficients : Fin 2 → ℚ[X] :=
  ![2 * (-34 - 6353 * X + 690355 * X ^ 2 - 1065613 * X ^ 3 +
      867876 * X ^ 4 - 438336 * X ^ 5 + 72576 * X ^ 6),
    2 * (X - 4) * (10 + 204 * X - 118195 * X ^ 2 + 146946 * X ^ 3 -
      142848 * X ^ 4 + 41472 * X ^ 5)]

theorem zagierEuler_coefficient_factors :
    zagierODECoeffQ 2 = X * zagierEulerDerivativeCoefficients 0 ∧
      zagierODECoeffQ 3 = X ^ 2 * zagierEulerDerivativeCoefficients 1 ∧
      zagierODECoeffQ 4 = X ^ 3 * zagierEulerDenominator := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [zagierODECoeffQ, zagierEulerDerivativeCoefficients, zagierEulerDenominator,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] <;> ring

/-- The powers used to regularize the fourteen series in their original order. -/
def holonomyRegularEulerWeights : Fin 14 → ℕ :=
  ![0, 0, 1, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0]

/-- The literal primitives, scaled derivatives, and pure seven series. -/
def holonomyRegularEulerSeries (g : PowerSeries ℚ) : Fin 14 → PowerSeries ℚ :=
  ![formalIntegral g, formalIntegral (formalShift g),
    PowerSeries.X * formalIntegral (formalSecondShift g),
    g, PowerSeries.X * g.derivativeFun, PowerSeries.X ^ 2 * g.derivativeFun.derivativeFun,
    PowerSeries.X ^ 3 * g.derivativeFun.derivativeFun.derivativeFun,
    1, pureB2Series, pureB3Series, pureB4Series, pureB5Series, pureB6Series, pureB7Series]

theorem holonomyRegularEulerSeries_eq (a b c : ℚ) (i : Fin 14) :
    holonomyRegularEulerSeries (symmetrizedDescent (a • hA + b • hB + c • hC)) i =
      PowerSeries.X ^ holonomyRegularEulerWeights i * cdtFourteenSeries a b c i := by
  fin_cases i <;> norm_num [holonomyRegularEulerSeries, holonomyRegularEulerWeights,
    cdtFourteenSeries, zagierAuxiliarySeries, Fin.append, Fin.addCases] <;> rfl

/-- A common polynomial denominator for the fourteen Euler equations. -/
def holonomyRegularEulerDenominator : ℚ[X] := 2 * (4 - X) * zagierEulerDenominator

theorem holonomyRegularEulerDenominator_constantCoeff :
    holonomyRegularEulerDenominator.coeff 0 = -128 := by
  norm_num [coeff_zero_eq_eval_zero, holonomyRegularEulerDenominator, zagierEulerDenominator]

/-- The polynomial numerator matrix, including the actual forcing and Taylor constants. -/
def holonomyRegularEulerNumerator (g : PowerSeries ℚ) (r : ℚ[X]) :
    Matrix (Fin 14) (Fin 14) ℚ[X] :=
  let q := zagierEulerDenominator
  let Q := holonomyRegularEulerDenominator
  let h := 2 * (4 - X)
  let p := 2 * q
  let g0 := C (PowerSeries.constantCoeff (R := ℚ) g)
  let g1 := C (PowerSeries.coeff (R := ℚ) 1 g)
  !![0, 0, 0, Q * X, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, Q, 0, 0, 0, -Q * g0, 0, 0, 0, 0, 0, 0;
    0, 0, Q, Q, 0, 0, 0, -Q * (g0 + g1 * X), 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, Q, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, Q, Q, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 2 * Q, Q, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, -h * X * zagierODECoeffQ 0, -h * zagierODECoeffQ 1,
      -h * zagierEulerDerivativeCoefficients 0, h * (3 * q - zagierEulerDerivativeCoefficients 1),
      h * X * r, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, p * X ^ 2, p * (2 - X), 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, p * (2 * X), -p, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, -p * (2 * X * (4 - X)), p * (4 - X), 0,
      p * (2 - X), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, q * (4 * X), -2 * q, 0, 0, q * (4 - X), 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, Q, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, Q, 0, 0, 0]

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "q" => (zagierEulerDenominator : PowerSeries ℚ)
local notation "Q" => (holonomyRegularEulerDenominator : PowerSeries ℚ)

theorem holonomyRegularEulerNumerator_mulVec_zagier (g : PowerSeries ℚ) (r : ℚ[X])
    (v : Fin 14 → PowerSeries ℚ) (i : Fin 7) :
    ((fun i j => (holonomyRegularEulerNumerator g r i j : PowerSeries ℚ)) *ᵥ v) (i.castAdd 7) =
      ![Q * x * v 3,
        Q * (v 3 - PowerSeries.C (R := ℚ) (PowerSeries.constantCoeff (R := ℚ) g) * v 7),
        Q * (v 2 + v 3 - (PowerSeries.C (R := ℚ) (PowerSeries.constantCoeff (R := ℚ) g) +
          PowerSeries.C (R := ℚ) (PowerSeries.coeff (R := ℚ) 1 g) * x) * v 7),
        Q * v 4, Q * (v 4 + v 5), Q * (2 * v 5 + v 6),
        2 * (4 - x) * (-(x * (zagierODECoeffQ 0 : PowerSeries ℚ) * v 3) -
          (zagierODECoeffQ 1 : PowerSeries ℚ) * v 4 -
          (zagierEulerDerivativeCoefficients 0 : PowerSeries ℚ) * v 5 +
          (3 * q - (zagierEulerDerivativeCoefficients 1 : PowerSeries ℚ)) * v 6 +
          x * (r : PowerSeries ℚ) * v 7)] i := by
  fin_cases i <;>
    dsimp only [holonomyRegularEulerNumerator, Matrix.mulVec, dotProduct, Fin.castAdd, Fin.natAdd,
      Fin.castLE, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ']
    simp only [← coeToPowerSeries.ringHom_apply, map_mul, map_add, map_sub, map_neg,
      map_pow, map_ofNat, map_zero, map_one]
    simp only [coeToPowerSeries.ringHom_apply, coe_C, coe_X]
    ring!

theorem holonomyRegularEulerNumerator_mulVec_pure (g : PowerSeries ℚ) (r : ℚ[X])
    (v : Fin 14 → PowerSeries ℚ) (i : Fin 7) :
    ((fun i j => (holonomyRegularEulerNumerator g r i j : PowerSeries ℚ)) *ᵥ v) (Fin.natAdd 7 i) =
      ![0,
        2 * q * (x ^ 2 * v 7 + (2 - x) * v 8),
        2 * q * (2 * x * v 7 - v 8),
        2 * q * (-2 * x * (4 - x) * v 7 + (4 - x) * v 8 + (2 - x) * v 10),
        q * (4 * x * v 7 - 2 * v 8 + (4 - x) * v 11), Q * v 9, Q * v 10] i := by
  fin_cases i <;>
    dsimp only [holonomyRegularEulerNumerator, Matrix.mulVec, dotProduct, Fin.castAdd, Fin.natAdd,
      Fin.castLE, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ']
    simp only [← coeToPowerSeries.ringHom_apply, map_mul, map_add, map_sub, map_neg,
      map_pow, map_ofNat, map_zero, map_one]
    simp only [coeToPowerSeries.ringHom_apply, coe_C, coe_X]
    ring!

theorem holonomyRegularEulerNumerator_mulVec (g : PowerSeries ℚ) (r : ℚ[X])
    (v : Fin 14 → PowerSeries ℚ) :
    (fun i j => (holonomyRegularEulerNumerator g r i j : PowerSeries ℚ)) *ᵥ v =
      ![Q * x * v 3,
        Q * (v 3 - PowerSeries.C (R := ℚ) (PowerSeries.constantCoeff (R := ℚ) g) * v 7),
        Q * (v 2 + v 3 - (PowerSeries.C (R := ℚ) (PowerSeries.constantCoeff (R := ℚ) g) +
          PowerSeries.C (R := ℚ) (PowerSeries.coeff (R := ℚ) 1 g) * x) * v 7),
        Q * v 4, Q * (v 4 + v 5), Q * (2 * v 5 + v 6),
        2 * (4 - x) * (-(x * (zagierODECoeffQ 0 : PowerSeries ℚ) * v 3) -
          (zagierODECoeffQ 1 : PowerSeries ℚ) * v 4 -
          (zagierEulerDerivativeCoefficients 0 : PowerSeries ℚ) * v 5 +
          (3 * q - (zagierEulerDerivativeCoefficients 1 : PowerSeries ℚ)) * v 6 +
          x * (r : PowerSeries ℚ) * v 7),
        0,
        2 * q * (x ^ 2 * v 7 + (2 - x) * v 8),
        2 * q * (2 * x * v 7 - v 8),
        2 * q * (-2 * x * (4 - x) * v 7 + (4 - x) * v 8 + (2 - x) * v 10),
        q * (4 * x * v 7 - 2 * v 8 + (4 - x) * v 11), Q * v 9, Q * v 10] := by
  funext i
  fin_cases i
  · exact holonomyRegularEulerNumerator_mulVec_zagier g r v 0
  · exact holonomyRegularEulerNumerator_mulVec_zagier g r v 1
  · exact holonomyRegularEulerNumerator_mulVec_zagier g r v 2
  · exact holonomyRegularEulerNumerator_mulVec_zagier g r v 3
  · exact holonomyRegularEulerNumerator_mulVec_zagier g r v 4
  · exact holonomyRegularEulerNumerator_mulVec_zagier g r v 5
  · exact holonomyRegularEulerNumerator_mulVec_zagier g r v 6
  · exact holonomyRegularEulerNumerator_mulVec_pure g r v 0
  · exact holonomyRegularEulerNumerator_mulVec_pure g r v 1
  · exact holonomyRegularEulerNumerator_mulVec_pure g r v 2
  · exact holonomyRegularEulerNumerator_mulVec_pure g r v 3
  · exact holonomyRegularEulerNumerator_mulVec_pure g r v 4
  · exact holonomyRegularEulerNumerator_mulVec_pure g r v 5
  · exact holonomyRegularEulerNumerator_mulVec_pure g r v 6

theorem holonomyRegularEuler_system_of_forcing (g : PowerSeries ℚ) (r : ℚ[X])
    (hg : zagierDescendedODE g = (r : PowerSeries ℚ)) (i : Fin 14) :
    (holonomyRegularEulerDenominator : PowerSeries ℚ) *
        powerSeriesEuler ℚ (holonomyRegularEulerSeries g i) =
      ((fun i j => (holonomyRegularEulerNumerator g r i j : PowerSeries ℚ)) *ᵥ
        holonomyRegularEulerSeries g) i := by
  have hI (f : PowerSeries ℚ) : D (formalIntegral f) = f := derivative_formalIntegral f
  have hQ : Q = 2 * (4 - x) * q := by
    change coeToPowerSeries.ringHom (2 * (4 - X) * zagierEulerDenominator) = _
    simp only [map_mul, map_sub, map_ofNat]
    simp only [coeToPowerSeries.ringHom_apply, coe_X]
  have h0 : (zagierODECoeffQ 0 : PowerSeries ℚ) * g +
      (zagierODECoeffQ 1 : PowerSeries ℚ) * D g +
      (x * (zagierEulerDerivativeCoefficients 0 : PowerSeries ℚ)) * D (D g) +
      (x ^ 2 * (zagierEulerDerivativeCoefficients 1 : PowerSeries ℚ)) * D (D (D g)) +
      (x ^ 3 * (zagierEulerDenominator : PowerSeries ℚ)) * D (D (D (D g))) =
      (r : PowerSeries ℚ) := by
    change (zagierODECoeffQ 0 : PowerSeries ℚ) * g +
      (zagierODECoeffQ 1 : PowerSeries ℚ) * D g +
      (zagierODECoeffQ 2 : PowerSeries ℚ) * D (D g) +
      (zagierODECoeffQ 3 : PowerSeries ℚ) * D (D (D g)) +
      (zagierODECoeffQ 4 : PowerSeries ℚ) * D (D (D (D g))) = _ at hg
    rw [zagierEuler_coefficient_factors.1, zagierEuler_coefficient_factors.2.1,
      zagierEuler_coefficient_factors.2.2] at hg
    simpa only [coe_mul, coe_pow, coe_X] using hg
  rw [holonomyRegularEulerNumerator_mulVec]
  fin_cases i
  · change Q * (x * D (formalIntegral g)) = Q * x * g
    rw [hI]
    ring
  · change Q * (x * D (formalIntegral (formalShift g))) =
      Q * (g - PowerSeries.C (R := ℚ) (PowerSeries.constantCoeff (R := ℚ) g) * 1)
    rw [hI, X_mul_formalShift, mul_one]
  · change Q * (x * D (x * formalIntegral (formalSecondShift g))) =
      Q * (x * formalIntegral (formalSecondShift g) + g -
        (PowerSeries.C (R := ℚ) (PowerSeries.constantCoeff (R := ℚ) g) +
          PowerSeries.C (R := ℚ) (PowerSeries.coeff (R := ℚ) 1 g) * x) * 1)
    rw [Derivation.leibniz, hI, PowerSeries.derivative_X]
    simp only [smul_eq_mul, mul_one]
    linear_combination Q * X_sq_mul_formalSecondShift g
  · change Q * (x * D g) = Q * (x * D g)
    rfl
  · change Q * (x * D (x * D g)) = Q * (x * D g + x ^ 2 * D (D g))
    rw [Derivation.leibniz, PowerSeries.derivative_X]
    simp only [smul_eq_mul]
    ring
  · change Q * (x * D (x ^ 2 * D (D g))) =
      Q * (2 * (x ^ 2 * D (D g)) + x ^ 3 * D (D (D g)))
    simp only [Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X,
      smul_eq_mul, nsmul_eq_mul]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
    ring
  · change Q * (x * D (x ^ 3 * D (D (D g)))) =
      2 * (4 - x) * (-(x * (zagierODECoeffQ 0 : PowerSeries ℚ) * g) -
        (zagierODECoeffQ 1 : PowerSeries ℚ) * (x * D g) -
        (zagierEulerDerivativeCoefficients 0 : PowerSeries ℚ) * (x ^ 2 * D (D g)) +
        (3 * q - (zagierEulerDerivativeCoefficients 1 : PowerSeries ℚ)) *
          (x ^ 3 * D (D (D g))) + x * (r : PowerSeries ℚ) * 1)
    simp only [hQ, Derivation.leibniz, Derivation.leibniz_pow, PowerSeries.derivative_X,
      smul_eq_mul, nsmul_eq_mul]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
    linear_combination 2 * (4 - x) * x * h0
  · change Q * (x * D 1) = 0
    simp
  · change Q * (x * D pureB2Series) = 2 * q * (x ^ 2 * 1 + (2 - x) * pureB2Series)
    rw [hQ]
    linear_combination 2 * q * pureB2Series_ode
  · change Q * (x * D pureB3Series) = 2 * q * (2 * x * 1 - pureB2Series)
    rw [hQ]
    linear_combination 2 * q * pureB3Series_first_order_ode
  · change Q * (x * D pureB4Series) =
      2 * q * (-2 * x * (4 - x) * 1 + (4 - x) * pureB2Series + (2 - x) * pureB4Series)
    rw [hQ]
    linear_combination 2 * q * pureB4Series_ode
  · change Q * (x * D pureB5Series) = q * (4 * x * 1 - 2 * pureB2Series + (4 - x) * pureB5Series)
    rw [hQ]
    linear_combination q * pureB5Series_first_order_ode
  · change Q * (x * D pureB6Series) = Q * pureB3Series
    rw [show x * D pureB6Series = pureB3Series from X_mul_derivative_pureB6Series]
  · change Q * (x * D pureB7Series) = Q * pureB4Series
    rw [show x * D pureB7Series = pureB4Series from X_mul_derivative_pureB7Series]

theorem holonomyRegularEuler_system (a b c : ℚ) (i : Fin 14) :
    let g := symmetrizedDescent (a • hA + b • hB + c • hC)
    (holonomyRegularEulerDenominator : PowerSeries ℚ) *
        powerSeriesEuler ℚ (holonomyRegularEulerSeries g i) =
      ((fun i j => (holonomyRegularEulerNumerator g
        (C b * zagierDescendedForcingB + C c * zagierDescendedForcingC) i j : PowerSeries ℚ)) *ᵥ
          holonomyRegularEulerSeries g) i := by
  apply holonomyRegularEuler_system_of_forcing
  simpa only [coe_add, coe_mul, coe_C, PowerSeries.smul_eq_C_mul] using
    zagierDescendedODE_symmetrizedDescent_h_linearCombination a b c

end DirichletL
