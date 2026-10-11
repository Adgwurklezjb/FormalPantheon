import Analysis.AnalyticLinearODEContinuation
import Analysis.FunctionsHCompanion

/-!
Continuation of CDT v2's original forced equation `defH`. The augmented
system continues the actual scalar solution with both forcing constants fixed.
This is an input to the continuation step of Lemma `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

/-- Continue an actual forced H-solution along any path in its regular locus. -/
theorem exists_analyticContinuationAlong_forcedH
    (γ : C(unitInterval, hForcedRegularSet)) (f : ℂ → ℂ) (b c : ℂ)
    (hf : AnalyticAt ℂ f (γ 0 : ℂ))
    (hfo : ∀ᶠ z in 𝓝 (γ 0 : ℂ), zagierSecondOrderODE f z = b + c / (1 - z)) :
    ∃ F : unitInterval → ℂ → ℂ,
      AnalyticContinuationAlong (fun t => (γ t : ℂ)) F ∧
      F 0 =ᶠ[𝓝 (γ 0 : ℂ)] f ∧
      ∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), zagierSecondOrderODE (F t) z = b + c / (1 - z) := by
  have hs : ∀ᶠ z in 𝓝 (γ 0 : ℂ),
      HasDerivAt (hForcedState f b c) (hForcedMatrix z *ᵥ hForcedState f b c z) z := by
    filter_upwards [hf.eventually_analyticAt, hfo,
      isOpen_hForcedRegularSet.mem_nhds (γ 0).property] with z hfz hze hz
    exact hasDerivAt_hForcedState_of_ode hfz hz hze
  obtain ⟨V, hV, hinit, hVo⟩ := hForcedSystem.exists_analyticContinuationAlong γ
    (hForcedState f b c) (analyticAt_hForcedState hf b c) hs
  have hconst (k : ℂ) :
      AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun _ _ => k) :=
    AnalyticContinuationAlong.const (continuous_subtype_val.comp γ.continuous)
      (fun _ => analyticAt_const)
  have hb : ∀ t, (fun z => V t z 2) =ᶠ[𝓝 (γ t : ℂ)] fun _ => b := by
    apply (hV 2).eq_of_preconnectedSpace (hconst b) (t₀ := 0)
    filter_upwards [hinit] with z hz
    exact congrFun hz (2 : Fin 4)
  have hc : ∀ t, (fun z => V t z 3) =ᶠ[𝓝 (γ t : ℂ)] fun _ => c := by
    apply (hV 3).eq_of_preconnectedSpace (hconst c) (t₀ := 0)
    filter_upwards [hinit] with z hz
    exact congrFun hz (3 : Fin 4)
  refine ⟨fun t z => V t z 0, hV 0, ?_, ?_⟩
  · filter_upwards [hinit] with z hz
    exact congrFun hz (0 : Fin 4)
  · intro t
    filter_upwards [eventually_hForcedODE_of_matrix (γ t).property (hVo t), hb t, hc t]
      with z hz hzb hzc
    simpa only [hzb, hzc] using hz

end DirichletL
