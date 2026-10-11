import Analysis.PureOriginalState

/-!
Recovery of B1 through B7 from the reduced original-coordinate state.
Source: CDT v2 `defB`, TeX 7327-7351, with the existing pullback identities.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- Recover the original B1 through B7 order from the reduced pure state. -/
noncomputable def pureOriginalReconstruct (x : ℂ) (v : Fin 7 → ℂ) : Fin 7 → ℂ :=
  ![v 0, 2 * mobiusCoordinate x * v 0 + (x - mobiusAnalyticInvolution x) * v 1,
    -v 2 / 2, (x - mobiusAnalyticInvolution x) * (2 * v 3 + v 2 / 2), v 4, v 5, v 6]

theorem analyticAt_pureOriginalReconstruct {X : ℂ → ℂ} {v : ℂ → Fin 7 → ℂ} {z : ℂ}
    (hX : AnalyticAt ℂ X z) (hv : AnalyticAt ℂ v z) (hX1 : X z ≠ 1) :
    AnalyticAt ℂ (fun w => pureOriginalReconstruct (X w) (v w)) z := by
  have hY := (analyticAt_mobiusCoordinate hX1).comp' hX
  have hw := (analyticAt_mobiusAnalyticInvolution hX1).comp' hX
  have hδ := hX.sub hw
  have hv' (i : Fin 7) := analyticAt_pi_iff.mp hv i
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact hv' 0
  · exact ((analyticAt_const.mul hY).mul (hv' 0)).add (hδ.mul (hv' 1))
  · exact (hv' 2).neg.div analyticAt_const (by norm_num)
  · exact hδ.mul ((analyticAt_const.mul (hv' 3)).add
      ((hv' 2).div analyticAt_const (by norm_num)))
  · exact hv' 4
  · exact hv' 5
  · exact hv' 6

theorem pureOriginalReconstruct_state_germ :
    (fun x => pureOriginalReconstruct x (pureOriginalState x)) =ᶠ[𝓝 (0 : ℂ)]
      fun x => pureSevenState (mobiusCoordinate x) := by
  filter_upwards [pureB2_pullback, pureB3_pullback_eq_clog_sq,
    pureB4_pullback_eq_pureFour] with x h2 h3 h4
  ext i
  fin_cases i
  · rfl
  · simpa only [pureOriginalReconstruct, pureOriginalState, pureSevenState,
      Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] using h2.symm
  · change -(-Complex.log (1 - x)) ^ 2 / 2 = pureB3 (mobiusCoordinate x)
    simpa only [neg_sq] using h3.symm
  · change (x - mobiusAnalyticInvolution x) *
      (2 * pureDilogarithm x + (-Complex.log (1 - x)) ^ 2 / 2) = pureB4 (mobiusCoordinate x)
    rw [h4]
    ring
  · rfl
  · rfl
  · rfl

end DirichletL
