import Analysis.PureFunctionCompanion

/-!
The pure-family differential matrix in the original x coordinate.
Source: CDT v2 `defB`, `defB5`, `defB67`, and `diffformulas`.
-/

namespace DirichletL

open scoped Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The reduced original-coordinate system for the seven pure initial functions. -/
noncomputable def pureOriginalMatrix (x : ℂ) : Matrix (Fin 7) (Fin 7) ℂ :=
  !![0, 0, 0, 0, 0, 0, 0;
    1 / (1 - x), 0, 0, 0, 0, 0, 0;
    0, 2 / (1 - x), 0, 0, 0, 0, 0;
    0, 1 / x, 0, 0, 0, 0, 0;
    0, 1 / (x - 1), 0, 0, (x - 2) / (2 * x * (x - 1)), 0, 0;
    0, 0, -(x - 2) / (2 * x * (x - 1)), 0, 0, 0, 0;
    0, 0, (x - 2) ^ 2 / (2 * (x - 1) ^ 2),
      2 * (x - 2) ^ 2 / (x - 1) ^ 2, 0, 0, 0]

theorem pureOriginalMatrix_mulVec (x : ℂ) (v : Fin 7 → ℂ) :
    pureOriginalMatrix x *ᵥ v =
      ![0, v 0 / (1 - x), 2 * v 1 / (1 - x), v 1 / x,
        v 1 / (x - 1) + (x - 2) / (2 * x * (x - 1)) * v 4,
        -(x - 2) / (2 * x * (x - 1)) * v 2,
        (x - 2) ^ 2 / (x - 1) ^ 2 * (2 * v 3 + v 2 / 2)] := by
  ext i
  fin_cases i <;> simp [pureOriginalMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    div_eq_mul_inv, mul_inv_rev] <;> ring

theorem analyticAt_pureOriginalMatrix {x : ℂ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    AnalyticAt ℂ pureOriginalMatrix x := by
  have hm : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hp : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hd : 2 * x * (x - 1) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hx0) hm
  have hs : (x - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have h2s : 2 * (x - 1) ^ 2 ≠ 0 := mul_ne_zero (by norm_num) hs
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [pureOriginalMatrix, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    fun_prop (disch := assumption)

end DirichletL
