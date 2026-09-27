import Analysis.AnalyticContinuation
import Analysis.AnalyticComposition

/-!
Local changes of variable for the continuations in CDT v2, Lemma `14functions`.
Full pullback germs ensure compatibility of independently chosen local inverses.
-/

namespace DirichletL.AnalyticContinuationAlong

open Filter
open scoped Topology

variable {T : Type*} [TopologicalSpace T] {γ : T → ℂ} {f : T → ℂ → ℂ}

theorem of_comp (hf : AnalyticContinuationAlong γ f) {φ : ℂ → ℂ}
    (hφ : ∀ t, AnalyticAt ℂ φ (γ t)) (hne : ∀ t, _root_.deriv φ (γ t) ≠ 0)
    {g : T → ℂ → ℂ} (hg : ∀ t, AnalyticAt ℂ (g t) (φ (γ t)))
    (he : ∀ t, (g t ∘ φ) =ᶠ[𝓝 (γ t)] f t) :
    AnalyticContinuationAlong (φ ∘ γ) g := by
  refine ⟨?_, hg, ?_⟩
  · exact continuous_iff_continuousAt.mpr fun t =>
      (hφ t).continuousAt.comp hf.continuous.continuousAt
  · intro t
    have hn := hf.continuous.continuousAt.tendsto.eventually (he t).eventually_nhds
    filter_upwards [hf.locally_eq t, hn] with s hs hns
    exact eventuallyEq_of_comp_of_analyticAt (hφ s) (hne s)
      ((he s).trans (hs.trans (Filter.EventuallyEq.symm hns)))

theorem exists_of_comp (hf : AnalyticContinuationAlong γ f) {φ : ℂ → ℂ}
    (hφ : ∀ t, AnalyticAt ℂ φ (γ t)) (hne : ∀ t, _root_.deriv φ (γ t) ≠ 0) :
    ∃ g : T → ℂ → ℂ, AnalyticContinuationAlong (φ ∘ γ) g ∧
      ∀ t, (g t ∘ φ) =ᶠ[𝓝 (γ t)] f t := by
  choose ψ hψ hψc hψl hψr using fun t => exists_analyticAt_localInverse (hφ t) (hne t)
  let g : T → ℂ → ℂ := fun t => f t ∘ ψ t
  have hg (t : T) : AnalyticAt ℂ (g t) (φ (γ t)) :=
    (hf.analytic t).comp_of_eq (hψ t) (hψc t)
  have he (t : T) : (g t ∘ φ) =ᶠ[𝓝 (γ t)] f t := by
    filter_upwards [hψl t] with z hz
    exact congrArg (f t) hz
  exact ⟨g, hf.of_comp hφ hne hg he, he⟩

end DirichletL.AnalyticContinuationAlong
