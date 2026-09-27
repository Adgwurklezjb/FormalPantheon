import Analysis.ZagierPullbackAnalytic
import Analysis.ZagierContinuationRepresentatives
import Analysis.AnalyticContinuationChangeOfVariable

/-!
Second-order continuation families lift to the actual fourth-order solution
covering under CDT v2's coordinate `y in x`, for the step in `14functions`.
-/

namespace DirichletL

open Filter Bundle
open scoped Topology

theorem exists_analyticContinuationAlong_zagierPullback
    {T : Type*} [TopologicalSpace T] {γ : T → ℂ} {f : T → ℂ → ℂ}
    (hf : AnalyticContinuationAlong γ f)
    (hE : ∀ t, zagierSecondOrderODE (f t) =ᶠ[𝓝 (γ t)] 0)
    (h₀ : ∀ t, γ t ≠ 0) (h₁ : ∀ t, γ t ≠ 1) (h₂ : ∀ t, γ t ≠ 2) :
    ∃ g : T → ℂ → ℂ, AnalyticContinuationAlong (mobiusCoordinate ∘ γ) g ∧
      (∀ t, zagierAnalyticODE (g t) =ᶠ[𝓝 (mobiusCoordinate (γ t))] 0) ∧
      ∀ t, (g t ∘ mobiusCoordinate) =ᶠ[𝓝 (γ t)] f t := by
  choose g hg hgo hgf using fun t => exists_zagierAnalyticODE_of_secondOrder
    (h₀ t) (h₁ t) (h₂ t) (hf.analytic t) (hE t)
  exact ⟨g, hf.of_comp (fun t => analyticAt_mobiusCoordinate (h₁ t))
    (fun t => deriv_mobiusCoordinate_ne_zero (h₀ t) (h₁ t) (h₂ t)) hg hgf, hgo, hgf⟩

theorem exists_zagierContinuation_of_secondOrder (b : zagierODERegularSet)
    {T : Type*} [TopologicalSpace T] {γ : T → ℂ} {f : T → ℂ → ℂ}
    (hf : AnalyticContinuationAlong γ f)
    (hE : ∀ t, zagierSecondOrderODE (f t) =ᶠ[𝓝 (γ t)] 0)
    (h₀ : ∀ t, γ t ≠ 0) (h₁ : ∀ t, γ t ≠ 1) (h₂ : ∀ t, γ t ≠ 2)
    (hreg : ∀ t, mobiusCoordinate (γ t) ∈ zagierODERegularSet) :
    ∃ u : T → ZagierContinuation b, Continuous u ∧ ∀ t,
      ((u t).proj : ℂ) = mobiusCoordinate (γ t) ∧ ∃ F : ℂ → ℂ,
        ((u t).snd : Germ (𝓝 ((u t).proj : ℂ)) ℂ) = F ∧
          (F ∘ mobiusCoordinate) =ᶠ[𝓝 (γ t)] f t := by
  obtain ⟨g, hg, hgo, hgf⟩ :=
    exists_analyticContinuationAlong_zagierPullback hf hE h₀ h₁ h₂
  let u : T → ZagierContinuation b := fun t =>
    ⟨⟨mobiusCoordinate (γ t), hreg t⟩, zagierSolutionGermOfFun (g t) (hg.analytic t) (hgo t)⟩
  refine ⟨u, continuous_zagierContinuation_of_analyticContinuation b hg (fun _ => rfl), ?_⟩
  exact fun t => ⟨rfl, g t, rfl, hgf t⟩

end DirichletL
