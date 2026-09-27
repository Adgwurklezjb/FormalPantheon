import Analysis.FunctionsGOriginalPrimitives

/-!
The actual initial state for the original-coordinate G primitive system.
Source: CDT v2 `defH`, `defG`, and `14functions`, TeX 7751-7768,
7861-7866, and 8044-8051. Prior meanings and exact state ordering:
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

/-- The two actual H branches, their original derivatives, one, and three direct primitives. -/
noncomputable def gPrimitiveOriginalState (f : ℂ → ℂ) (K : Fin 3 → ℂ → ℂ)
    (x : ℂ) : Fin 8 → ℂ :=
  ![f x, deriv f x, f (mobiusAnalyticInvolution x), deriv f (mobiusAnalyticInvolution x),
    1, K 0 x, K 1 x, K 2 x]

theorem analyticAt_gPrimitiveOriginalState {f : ℂ → ℂ} {K : Fin 3 → ℂ → ℂ} {x : ℂ}
    (hx : x ≠ 1) (hf : AnalyticAt ℂ f x)
    (hw : AnalyticAt ℂ f (mobiusAnalyticInvolution x))
    (hK : ∀ j, AnalyticAt ℂ (K j) x) :
    AnalyticAt ℂ (gPrimitiveOriginalState f K) x := by
  have hi := analyticAt_mobiusAnalyticInvolution hx
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact hf
  · exact hf.deriv
  · exact hw.comp hi
  · exact hw.deriv.comp hi
  · exact analyticAt_const
  · exact hK 0
  · exact hK 1
  · exact hK 2

theorem hasDerivAt_gPrimitiveOriginalState_of_ode
    {f : ℂ → ℂ} {K : Fin 3 → ℂ → ℂ} {x b c k0 k1 : ℂ}
    (hx : x ∈ hForcedRegularSet)
    (hwreg : mobiusAnalyticInvolution x ∈ hForcedRegularSet)
    (hf : AnalyticAt ℂ f x) (hw : AnalyticAt ℂ f (mobiusAnalyticInvolution x))
    (hfo : zagierSecondOrderODE f x = b + c / (1 - x))
    (hwo : zagierSecondOrderODE f (mobiusAnalyticInvolution x) =
      b + c / (1 - mobiusAnalyticInvolution x))
    (hK : ∀ j, HasDerivAt (K j) (deriv mobiusCoordinate x *
      gPrimitiveIntegrand (fun _ => f x + f (mobiusAnalyticInvolution x))
        k0 k1 j (mobiusCoordinate x)) x) :
    HasDerivAt (gPrimitiveOriginalState f K)
      (gPrimitiveMatrix b c k0 k1 x *ᵥ gPrimitiveOriginalState f K x) x := by
  have hi := (analyticAt_mobiusAnalyticInvolution
    ((mem_hForcedRegularSet_iff x).mp hx).2.2).differentiableAt.hasDerivAt
  have hu := hasDerivAt_pi.mp (hasDerivAt_hForcedState_of_ode hf hx hfo) 1
  have hv := hasDerivAt_pi.mp (hasDerivAt_hForcedState_of_ode hw hwreg hwo) 1
  rw [gPrimitiveMatrix_mulVec]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hf.differentiableAt.hasDerivAt
  · simpa [gPrimitiveOriginalState, hForcedState] using hu
  · simpa [gPrimitiveOriginalState, mul_comm] using hw.differentiableAt.hasDerivAt.comp x hi
  · simpa [gPrimitiveOriginalState, hForcedState, mul_comm] using hv.comp x hi
  · exact hasDerivAt_const x 1
  · simpa [gPrimitiveOriginalState, gPrimitiveIntegrand] using hK 0
  · simpa [gPrimitiveOriginalState, gPrimitiveIntegrand] using hK 1
  · simpa [gPrimitiveOriginalState, gPrimitiveIntegrand] using hK 2

theorem exists_analytic_gPrimitiveOriginal_state (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ v : ℂ → Fin 8 → ℂ, AnalyticOnNhd ℂ v (Metric.ball 0 (1 / 2)) ∧
      v =ᶠ[𝓝 (0 : ℂ)]
        gPrimitiveState (hLinearCombinationAnalytic a b c)
          (fun j => zagierAuxiliaryFunctions
            (symmetrizedDescent (a • hA + b • hB + c • hC)) (j.castAdd 4)) ∧
      ∀ x : ℂ, ‖x‖ < 1 / 2 → x ≠ 0 → x ≠ 1 / 9 → x ≠ -1 / 8 →
        HasDerivAt v (gPrimitiveMatrix (b : ℂ) (c : ℂ)
          (gLinearCombinationAnalytic a b c 0) (deriv (gLinearCombinationAnalytic a b c) 0)
          x *ᵥ v x) x := by
  obtain ⟨K, hKa, _, hKd, hKgerm⟩ := exists_analytic_gPrimitiveOriginal a b c hrel
  have hxne (x : ℂ) (hx : ‖x‖ < 1 / 2) : x ≠ 1 := by
    intro he
    simp only [he, norm_one] at hx
    norm_num at hx
  refine ⟨gPrimitiveOriginalState (hLinearCombinationAnalytic a b c) K, ?_, ?_, ?_⟩
  · intro x hx
    have hxn : ‖x‖ < 1 / 2 := by simpa using hx
    exact analyticAt_gPrimitiveOriginalState (hxne x hxn)
      (analyticAt_hLinearCombinationAnalytic a b c hrel (hxn.trans (by norm_num)))
      (analyticAt_hLinearCombinationAnalytic a b c hrel
        (norm_mobiusAnalyticInvolution_lt_one hxn)) (fun j => hKa j x hx)
  · filter_upwards [hKgerm 0, hKgerm 1, hKgerm 2] with x hx0 hx1 hx2
    simp only [gPrimitiveOriginalState, gPrimitiveState, hx0, hx1, hx2]
  · intro x hx hx0 hx9 hx8
    apply hasDerivAt_gPrimitiveOriginalState_of_ode
      ((mem_hForcedRegularSet_iff x).mpr ⟨hx0, hx9, hxne x hx⟩)
      (mobiusAnalyticInvolution_mem_hForcedRegularSet_of_ne hx0 (hxne x hx) hx8)
      (analyticAt_hLinearCombinationAnalytic a b c hrel (hx.trans (by norm_num)))
      (analyticAt_hLinearCombinationAnalytic a b c hrel
        (norm_mobiusAnalyticInvolution_lt_one hx))
      (hLinearCombinationAnalytic_ode a b c hrel (hx.trans (by norm_num)))
      (hLinearCombinationAnalytic_ode a b c hrel
        (norm_mobiusAnalyticInvolution_lt_one hx))
    intro j
    simpa only [gPrimitiveOriginalIntegrand_eq_of_ne a b c j hx0] using hKd j x hx

end DirichletL
