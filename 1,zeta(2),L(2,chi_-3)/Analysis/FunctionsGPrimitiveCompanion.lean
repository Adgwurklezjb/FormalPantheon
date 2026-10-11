import Analysis.FunctionsGPrimitives
import Analysis.FunctionsGContinuation

/-!
The simultaneous two-sheet and primitive system for CDT v2, Lemma `14functions`.
Both original H branches and the three normalized primitives are continued
in the x coordinate, with the original subtraction constants fixed.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isOpen_zagierPullbackRegularSet : IsOpen zagierPullbackRegularSet := by
  simpa only [compl_compl] using finite_compl_zagierPullbackRegularSet.isClosed.isOpen_compl

/-- State order: H, H', the other H branch, its original derivative, 1, and three primitives. -/
noncomputable def gPrimitiveMatrix (b c k0 k1 x : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  !![0, 1, 0, 0, 0, 0, 0, 0;
    hForcedMatrix x 1 0, hForcedMatrix x 1 1, 0, 0,
      b * hForcedMatrix x 1 2 + c * hForcedMatrix x 1 3, 0, 0, 0;
    0, 0, 0, deriv mobiusAnalyticInvolution x, 0, 0, 0, 0;
    0, 0, deriv mobiusAnalyticInvolution x * hForcedMatrix (mobiusAnalyticInvolution x) 1 0,
      deriv mobiusAnalyticInvolution x * hForcedMatrix (mobiusAnalyticInvolution x) 1 1,
      deriv mobiusAnalyticInvolution x *
        (b * hForcedMatrix (mobiusAnalyticInvolution x) 1 2 +
          c * hForcedMatrix (mobiusAnalyticInvolution x) 1 3), 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    deriv mobiusCoordinate x, 0, deriv mobiusCoordinate x, 0, 0, 0, 0, 0;
    deriv mobiusCoordinate x / mobiusCoordinate x, 0,
      deriv mobiusCoordinate x / mobiusCoordinate x, 0,
      -k0 * deriv mobiusCoordinate x / mobiusCoordinate x, 0, 0, 0;
    deriv mobiusCoordinate x / mobiusCoordinate x ^ 2, 0,
      deriv mobiusCoordinate x / mobiusCoordinate x ^ 2, 0,
      -(k0 + k1 * mobiusCoordinate x) * deriv mobiusCoordinate x / mobiusCoordinate x ^ 2,
      0, 0, 0]

set_option maxHeartbeats 800000 in
theorem gPrimitiveMatrix_mulVec (b c k0 k1 x : ℂ) (v : Fin 8 → ℂ) :
    gPrimitiveMatrix b c k0 k1 x *ᵥ v =
      ![v 1, (hForcedMatrix x *ᵥ ![v 0, v 1, b * v 4, c * v 4]) 1,
        deriv mobiusAnalyticInvolution x * v 3,
        deriv mobiusAnalyticInvolution x *
          (hForcedMatrix (mobiusAnalyticInvolution x) *ᵥ ![v 2, v 3, b * v 4, c * v 4]) 1,
        0, deriv mobiusCoordinate x * (v 0 + v 2),
        deriv mobiusCoordinate x * ((v 0 + v 2 - k0 * v 4) / mobiusCoordinate x),
        deriv mobiusCoordinate x *
          ((v 0 + v 2 - k0 * v 4 - k1 * mobiusCoordinate x * v 4) / mobiusCoordinate x ^ 2)] := by
  ext i
  fin_cases i <;> simp [gPrimitiveMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    div_eq_mul_inv] <;> ring

theorem gPrimitiveMatrix_mulVec_integrals (b c k0 k1 x : ℂ) (v : Fin 8 → ℂ) (j : Fin 3) :
    (gPrimitiveMatrix b c k0 k1 x *ᵥ v) (Fin.natAdd 5 j) =
      deriv mobiusCoordinate x *
        gPrimitiveIntegrand (fun _ => v 0 + v 2) (k0 * v 4) (k1 * v 4) j
          (mobiusCoordinate x) := by
  rw [gPrimitiveMatrix_mulVec]
  fin_cases j
  · rfl
  · rfl
  · change deriv mobiusCoordinate x *
        ((v 0 + v 2 - k0 * v 4 - k1 * mobiusCoordinate x * v 4) / mobiusCoordinate x ^ 2) =
      deriv mobiusCoordinate x *
        ((v 0 + v 2 - k0 * v 4 - (k1 * v 4) * mobiusCoordinate x) / mobiusCoordinate x ^ 2)
    ring

theorem analyticOnNhd_gPrimitiveMatrix (b c k0 k1 : ℂ) :
    AnalyticOnNhd ℂ (gPrimitiveMatrix b c k0 k1) zagierPullbackRegularSet := by
  intro x hx
  have hi := analyticAt_mobiusAnalyticInvolution hx.1
  have hY := analyticAt_mobiusCoordinate hx.1
  have hdi := hi.deriv
  have hdY := hY.deriv
  have hY0 := ((mem_zagierODERegularSet_iff _).mp hx.2).1
  have hY2 := pow_ne_zero 2 hY0
  have hF := analyticOnNhd_hForcedMatrix
    x (mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet hx)
  have hFi := (analyticOnNhd_hForcedMatrix (mobiusAnalyticInvolution x)
    (mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet
      (mobiusAnalyticInvolution_mem_zagierPullbackRegularSet hx))).comp hi
  have hFj (j : Fin 4) := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hF 1) j
  have hFij (j : Fin 4) := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hFi 1) j
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [gPrimitiveMatrix, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    fun_prop (disch := assumption)

/-- The analytic matrix data for simultaneous continuation of the trace and its primitives. -/
noncomputable def gPrimitiveSystem (b c k0 k1 : ℂ) : AnalyticMatrixODE (Fin 8) where
  domain := zagierPullbackRegularSet
  isOpen_domain := isOpen_zagierPullbackRegularSet
  matrix := gPrimitiveMatrix b c k0 k1
  analytic := analyticOnNhd_gPrimitiveMatrix b c k0 k1

/-- The actual two-sheet values and the three primitive pullbacks. -/
noncomputable def gPrimitiveState (f : ℂ → ℂ) (J : Fin 3 → ℂ → ℂ) (x : ℂ) : Fin 8 → ℂ :=
  ![f x, deriv f x, f (mobiusAnalyticInvolution x), deriv f (mobiusAnalyticInvolution x),
    1, J 0 (mobiusCoordinate x), J 1 (mobiusCoordinate x), J 2 (mobiusCoordinate x)]

theorem gPrimitiveState_integrals (f : ℂ → ℂ) (J : Fin 3 → ℂ → ℂ) (x : ℂ) (j : Fin 3) :
    gPrimitiveState f J x (Fin.natAdd 5 j) = J j (mobiusCoordinate x) := by
  fin_cases j <;> rfl

theorem analyticAt_gPrimitiveState {f : ℂ → ℂ} {J : Fin 3 → ℂ → ℂ} {x : ℂ}
    (hx : x ≠ 1) (hf : AnalyticAt ℂ f x)
    (hw : AnalyticAt ℂ f (mobiusAnalyticInvolution x))
    (hJ : ∀ j, AnalyticAt ℂ (J j) (mobiusCoordinate x)) :
    AnalyticAt ℂ (gPrimitiveState f J) x := by
  have hi := analyticAt_mobiusAnalyticInvolution hx
  have hY := analyticAt_mobiusCoordinate hx
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact hf
  · exact hf.deriv
  · exact hw.comp hi
  · exact hw.deriv.comp hi
  · exact analyticAt_const
  · exact (hJ 0).comp hY
  · exact (hJ 1).comp hY
  · exact (hJ 2).comp hY

theorem hasDerivAt_gPrimitiveState_of_ode {f G : ℂ → ℂ} {J : Fin 3 → ℂ → ℂ}
    {x b c k0 k1 : ℂ} (hx : x ∈ zagierPullbackRegularSet)
    (hf : AnalyticAt ℂ f x) (hw : AnalyticAt ℂ f (mobiusAnalyticInvolution x))
    (hfo : zagierSecondOrderODE f x = b + c / (1 - x))
    (hwo : zagierSecondOrderODE f (mobiusAnalyticInvolution x) =
      b + c / (1 - mobiusAnalyticInvolution x))
    (he : G (mobiusCoordinate x) = f x + f (mobiusAnalyticInvolution x))
    (hJ : ∀ j, HasDerivAt (J j) (gPrimitiveIntegrand G k0 k1 j (mobiusCoordinate x))
      (mobiusCoordinate x)) :
    HasDerivAt (gPrimitiveState f J)
      (gPrimitiveMatrix b c k0 k1 x *ᵥ gPrimitiveState f J x) x := by
  have hi := (analyticAt_mobiusAnalyticInvolution hx.1).differentiableAt.hasDerivAt
  have hY := (analyticAt_mobiusCoordinate hx.1).differentiableAt.hasDerivAt
  have hu := hasDerivAt_pi.mp (hasDerivAt_hForcedState_of_ode hf
    (mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet hx) hfo) 1
  have hv := hasDerivAt_pi.mp (hasDerivAt_hForcedState_of_ode hw
    (mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet
      (mobiusAnalyticInvolution_mem_zagierPullbackRegularSet hx)) hwo) 1
  rw [gPrimitiveMatrix_mulVec]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hf.differentiableAt.hasDerivAt
  · simpa [gPrimitiveState, hForcedState] using hu
  · simpa [gPrimitiveState, mul_comm] using hw.differentiableAt.hasDerivAt.comp x hi
  · simpa [gPrimitiveState, hForcedState, mul_comm] using hv.comp x hi
  · exact hasDerivAt_const x 1
  · simpa [gPrimitiveState, gPrimitiveIntegrand, he, mul_comm] using (hJ 0).comp x hY
  · simpa [gPrimitiveState, gPrimitiveIntegrand, he, mul_comm] using (hJ 1).comp x hY
  · simpa [gPrimitiveState, gPrimitiveIntegrand, he, mul_comm] using (hJ 2).comp x hY

end DirichletL
