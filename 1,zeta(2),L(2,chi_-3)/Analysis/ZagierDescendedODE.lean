import Analysis.ZagierODEPolynomials

/-!
The fourth-order descended operator in CDT v2, equation `explicitode`.
The displayed polynomial coefficients are lifted to `ℚ`. The operator has
the exact formal action on rational power series.
`ZagierDescentEquation.lean` proves the all-index equation for the descended
Zagier series; analytic continuation is supplied by later owners.
-/

namespace DirichletL

open Polynomial

/-- CDT v2 equation `explicitode`, with all five coefficients over `ℚ`. -/
noncomputable def zagierODECoeffQ : Fin 5 → ℚ[X] :=
  ![-18 * (3 + 126 * X - 712 * X ^ 2 + 360 * X ^ 3),
    2 * (-2 - 2761 * X + 141632 * X ^ 2 - 280328 * X ^ 3 + 176412 * X ^ 4 -
      95616 * X ^ 5 + 20736 * X ^ 6),
    2 * X * (-34 - 6353 * X + 690355 * X ^ 2 - 1065613 * X ^ 3 + 867876 * X ^ 4 -
      438336 * X ^ 5 + 72576 * X ^ 6),
    2 * (X - 4) * X ^ 2 * (10 + 204 * X - 118195 * X ^ 2 + 146946 * X ^ 3 -
      142848 * X ^ 4 + 41472 * X ^ 5),
    (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) *
      (-1 + 118 * X - 122 * X ^ 2 + 144 * X ^ 3)]

/-! The rational lift is exactly the previously recorded complex coefficient
table after coefficientwise embedding. -/
theorem map_zagierODECoeffQ (i : Fin 5) :
    Polynomial.map (algebraMap ℚ ℂ) (zagierODECoeffQ i) = zagierODECoeff i := by
  fin_cases i <;>
    norm_num [zagierODECoeffQ, zagierODECoeff, zagierSingularCubic,
      Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_C]

private noncomputable def zagierODECoeffQSeries (i : Fin 5) : PowerSeries ℚ :=
  (zagierODECoeffQ i : PowerSeries ℚ)

/-- The formal fourth-order operator with the rational `explicitode` coefficients. -/
noncomputable def zagierDescendedODE (f : PowerSeries ℚ) : PowerSeries ℚ :=
  zagierODECoeffQSeries 0 * f +
    zagierODECoeffQSeries 1 * f.derivativeFun +
    zagierODECoeffQSeries 2 * f.derivativeFun.derivativeFun +
    zagierODECoeffQSeries 3 * f.derivativeFun.derivativeFun.derivativeFun +
    zagierODECoeffQSeries 4 * f.derivativeFun.derivativeFun.derivativeFun.derivativeFun

end DirichletL
