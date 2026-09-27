import Arithmetic.LevelSixEtaCusps

/-!
Exact weights, multipliers, and cusp slopes for f^2, x*f^2, and x^2*f^2,
where f and x are the case C eta products in Zagier (2009), Section 5,
PDF page 8. The cusp slopes here are rational inequalities only.
-/

namespace DirichletL

/-- Eta-square exponents for the three weight-two products. -/
def zagierEtaExponents : Fin 3 → Fin 4 → ℤ :=
  ![![-3, 6, 1, -2], ![-1, 2, -1, 2], ![1, -2, -3, 6]]

theorem sum_zagierEtaExponents (r : Fin 3) : ∑ j, zagierEtaExponents r j = 2 := by
  fin_cases r <;> decide

theorem zagierEtaExponents_eq (r : Fin 3) (j : Fin 4) :
    zagierEtaExponents r j =
      zagierEtaExponents 0 j + (r.val : ℤ) * (![2, -4, -2, 4] : Fin 4 → ℤ) j := by
  fin_cases r <;> fin_cases j <;> decide

theorem zagierEtaExponents_generator (r : Fin 3) (b : Bool) (i : Fin 12) :
    12 ∣ ∑ j, zagierEtaExponents r j * modularWordExponent (levelSixEtaWord b i j) := by
  fin_cases r <;> cases b <;> fin_cases i <;> decide

theorem zagierEtaExponents_cusp_nonneg (r : Fin 3) (i : Fin 12) :
    (0 : ℚ) ≤ ∑ j, (zagierEtaExponents r j : ℚ) *
      ((levelSixEtaCuspData i j).numerator : ℚ) /
        ((levelSixEtaCuspData i j).denominator : ℚ) := by
  fin_cases r <;> fin_cases i <;>
    norm_num [zagierEtaExponents, levelSixEtaCuspData, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]

end DirichletL
