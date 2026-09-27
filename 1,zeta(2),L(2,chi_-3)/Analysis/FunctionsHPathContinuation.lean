import Analysis.FunctionsGContinuation
import Analysis.AnalyticContinuationDifference

/-!
Actual forced H continuation on original regular paths, retaining the full
initial germ and forcing in CDT v2, `defH` and `14functions`.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

theorem exists_analyticContinuationAlong_forcedH_path {x y : zagierPullbackRegularSet}
    (γ : Path x y) (f : ℂ → ℂ) (b c : ℂ) (hf : AnalyticAt ℂ f (x : ℂ))
    (hfo : ∀ᶠ z in 𝓝 (x : ℂ), zagierSecondOrderODE f z = b + c / (1 - z)) :
    ∃ F : I → ℂ → ℂ, AnalyticContinuationAlong (fun t => (γ t : ℂ)) F ∧
      F 0 =ᶠ[𝓝 (x : ℂ)] f ∧
      ∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), zagierSecondOrderODE (F t) z = b + c / (1 - z) := by
  let δ : C(I, hForcedRegularSet) := {
    toFun t := ⟨(γ t : ℂ), mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet (γ t).property⟩
    continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _ }
  have hδ0 : (δ 0 : ℂ) = (x : ℂ) := congrArg Subtype.val γ.source
  obtain ⟨F, hF, hF0, hFo⟩ := exists_analyticContinuationAlong_forcedH δ f b c
    (by simpa only [hδ0] using hf) (by simpa only [hδ0] using hfo)
  exact ⟨F, hF, by simpa only [hδ0] using hF0, hFo⟩

theorem exists_forcedH_conjugate_nontrivial {x y : zagierPullbackRegularSet}
    (η : Path x y) (τ : Path y y) (f : ℂ → ℂ) (b c : ℂ)
    (hf : AnalyticAt ℂ f (x : ℂ))
    (hfo : ∀ᶠ z in 𝓝 (x : ℂ), zagierSecondOrderODE f z = b + c / (1 - z))
    {G H : I → ℂ → ℂ} (hG : AnalyticContinuationAlong (fun t => (η t : ℂ)) G)
    (hH : AnalyticContinuationAlong (fun t => (τ t : ℂ)) H)
    (hG0 : G 0 =ᶠ[𝓝 (x : ℂ)] f) (hH0 : H 0 =ᶠ[𝓝 (y : ℂ)] G 1)
    (hne : ¬H 1 =ᶠ[𝓝 (y : ℂ)] H 0) :
    ∃ F : I → ℂ → ℂ,
      AnalyticContinuationAlong (fun t => (((η.trans τ).trans η.symm) t : ℂ)) F ∧
      F 0 =ᶠ[𝓝 (x : ℂ)] f ∧
      (∀ t, ∀ᶠ z in 𝓝 (((η.trans τ).trans η.symm) t : ℂ),
        zagierSecondOrderODE (F t) z = b + c / (1 - z)) ∧
      ¬F 1 =ᶠ[𝓝 (x : ℂ)] F 0 := by
  obtain ⟨F, hF, hF0, hFo⟩ :=
    exists_analyticContinuationAlong_forcedH_path ((η.trans τ).trans η.symm) f b c hf hfo
  refine ⟨F, hF, hF0, hFo, ?_⟩
  intro he
  exact hne (hF.end_eq_of_conjugate η τ Subtype.val hG hH
    (hF0.trans hG0.symm) hH0.symm he)

end DirichletL
