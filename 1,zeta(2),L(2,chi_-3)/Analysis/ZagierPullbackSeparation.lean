import Analysis.ZagierConjugateAnalytic
import Analysis.ZagierPullbackRegularity

/-!
Separation of the two analytic summands in CDT v2's `explicitode`.
The joint derivative certificate implements the direct-sum step in `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

/-- The rows of E, E', C, C' on the ordinary four-jet. -/
noncomputable def zagierJointJetMatrix (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![9 * z - 3, 1 - 20 * z + 27 * z ^ 2, z * (1 - z) * (1 - 9 * z), 0;
    9, 63 * z - 23, 2 * (1 - 20 * z + 27 * z ^ 2), z * (1 - z) * (1 - 9 * z);
    3 * (2 * z + 1), (z - 1) * (8 * z ^ 2 - 16 * z - 1),
      z * (z - 1) ^ 2 * (8 * z + 1), 0;
    6, 24 * z ^ 2 - 42 * z + 18, 40 * z ^ 3 - 69 * z ^ 2 + 27 * z + 2,
      z * (z - 1) ^ 2 * (8 * z + 1)]

theorem det_zagierJointJetMatrix (z : ℂ) :
    (zagierJointJetMatrix z).det = 36 * z ^ 2 * (z - 1) ^ 2 *
      (144 * z ^ 6 - 122 * z ^ 5 + 240 * z ^ 4 - 237 * z ^ 3 +
        121 * z ^ 2 - 3 * z + 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply]
  dsimp only [zagierJointJetMatrix, Fin.succAbove]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Fin.lt_def, Fin.le_def,
    show (2 : Fin 3) ≠ 0 by decide]
  ring

theorem det_zagierJointJetMatrix_coordinate {z : ℂ} (hz : z ≠ 1) :
    (zagierJointJetMatrix z).det =
      36 * z ^ 2 * (z - 1) ^ 5 * zagierSingularCubic.eval (mobiusCoordinate z) := by
  rw [det_zagierJointJetMatrix]
  simp only [zagierSingularCubic, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg,
    Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_X, mobiusCoordinate]
  field_simp [sub_ne_zero.mpr hz]
  ring

theorem det_zagierJointJetMatrix_ne_zero {z : ℂ} (hz : z ≠ 1)
    (hreg : mobiusCoordinate z ∈ zagierODERegularSet) :
    (zagierJointJetMatrix z).det ≠ 0 := by
  rw [det_zagierJointJetMatrix_coordinate hz]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (mobiusCoordinate_regular_ne_zero_two hreg).1))
      (pow_ne_zero _ (sub_ne_zero.mpr hz)))
        ((mem_zagierODERegularSet_iff _).mp hreg).2.2.2

theorem zagierSecondOrder_leading_ne_zero_of_pullback_regular {z : ℂ}
    (hz : z ≠ 1) (hreg : mobiusCoordinate z ∈ zagierODERegularSet) :
    z * (1 - z) * (1 - 9 * z) ≠ 0 ∧ z * (z - 1) ^ 2 * (8 * z + 1) ≠ 0 := by
  have hz₀ := (mobiusCoordinate_regular_ne_zero_two hreg).1
  have hY := ((mem_zagierODERegularSet_iff _).mp hreg).2.2.1
  constructor
  · refine mul_ne_zero (mul_ne_zero hz₀ (sub_ne_zero.mpr hz.symm)) ?_
    intro he
    have hz₉ : z = 1 / 9 := by linear_combination -(1 / 9 : ℂ) * he
    exact hY (by rw [hz₉, mobiusCoordinate_one_div_nine])
  · refine mul_ne_zero (mul_ne_zero hz₀ (pow_ne_zero _ (sub_ne_zero.mpr hz))) ?_
    intro he
    have hz₈ : z = -1 / 8 := by linear_combination (1 / 8 : ℂ) * he
    apply hY
    rw [hz₈]
    norm_num [mobiusCoordinate]

theorem zagierJointJetMatrix_mulVec_state {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) :
    (zagierJointJetMatrix z).mulVec (zagierODEState f z) =
      ![zagierSecondOrderODE f z, deriv (zagierSecondOrderODE f) z,
        zagierConjugateAnalyticODE f z, deriv (zagierConjugateAnalyticODE f) z] := by
  rw [(hasDerivAt_zagierSecondOrderODE hf).deriv,
    (hasDerivAt_zagierConjugateAnalyticODE hf).deriv]
  ext i
  fin_cases i <;>
    simp [zagierJointJetMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      zagierODEState, zagierSecondOrderODE, zagierConjugateAnalyticODE] <;> ring

theorem eventuallyEq_zero_of_zagierSecondOrder_and_conjugate {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 1) (hreg : mobiusCoordinate z ∈ zagierODERegularSet)
    (hf : AnalyticAt ℂ f z) (hE : zagierSecondOrderODE f =ᶠ[𝓝 z] 0)
    (hC : zagierConjugateAnalyticODE f =ᶠ[𝓝 z] 0) : f =ᶠ[𝓝 z] 0 := by
  have hM := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (det_zagierJointJetMatrix_ne_zero hz hreg))
  have hs : zagierODEState f z = 0 := by
    apply Matrix.mulVec_injective_of_isUnit hM
    rw [zagierJointJetMatrix_mulVec_state hf, Matrix.mulVec_zero]
    simp [hE.self_of_nhds, hC.self_of_nhds, hE.deriv.self_of_nhds,
      hC.deriv.self_of_nhds]
  exact eventuallyEq_zero_of_analytic_secondOrder_ode
    (a := fun w => w * (1 - w) * (1 - 9 * w))
    (b := fun w => 1 - 20 * w + 27 * w ^ 2) (c := fun w => 9 * w - 3)
    (by fun_prop) (by fun_prop) (by fun_prop)
    (zagierSecondOrder_leading_ne_zero_of_pullback_regular hz hreg).1 hf
    (congr_fun hs 0) (congr_fun hs 1) hE

end DirichletL
