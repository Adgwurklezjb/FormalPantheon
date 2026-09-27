import Analysis.ZagierPullbackTransport
import Analysis.ZagierConjugateAnalytic

/-!
Preservation of the two second-order summands under actual fourth-order transport.
This supplies the invariant summands over the x-plane in CDT v2, `14functions`.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

namespace AnalyticContinuationAlong

variable {T : Type*} [TopologicalSpace T] {γ : T → ℂ} {f : T → ℂ → ℂ}

theorem zagierSecondOrderODE (hf : AnalyticContinuationAlong γ f) :
    AnalyticContinuationAlong γ (fun t => DirichletL.zagierSecondOrderODE (f t)) := by
  have ha : AnalyticContinuationAlong γ (fun _ z => z * (1 - z) * (1 - 9 * z)) :=
    .const hf.continuous (fun _ => by fun_prop)
  have hb : AnalyticContinuationAlong γ (fun _ z => 1 - 20 * z + 27 * z ^ 2) :=
    .const hf.continuous (fun _ => by fun_prop)
  have hc : AnalyticContinuationAlong γ (fun _ z => 9 * z - 3) :=
    .const hf.continuous (fun _ => by fun_prop)
  exact ((ha.mul hf.deriv.deriv).add (hb.mul hf.deriv)).add (hc.mul hf)

theorem zagierConjugateAnalyticODE (hf : AnalyticContinuationAlong γ f) :
    AnalyticContinuationAlong γ (fun t => DirichletL.zagierConjugateAnalyticODE (f t)) := by
  have ha : AnalyticContinuationAlong γ (fun _ z => z * (z - 1) ^ 2 * (8 * z + 1)) :=
    .const hf.continuous (fun _ => by fun_prop)
  have hb : AnalyticContinuationAlong γ (fun _ z => (z - 1) * (8 * z ^ 2 - 16 * z - 1)) :=
    .const hf.continuous (fun _ => by fun_prop)
  have hc : AnalyticContinuationAlong γ (fun _ z => 3 * (2 * z + 1)) :=
    .const hf.continuous (fun _ => by fun_prop)
  exact ((ha.mul hf.deriv.deriv).add (hb.mul hf.deriv)).add (hc.mul hf)

theorem zagierSecondOrderODE_eq_zero [PreconnectedSpace T]
    (hf : AnalyticContinuationAlong γ f) {t₀ : T}
    (he : DirichletL.zagierSecondOrderODE (f t₀) =ᶠ[𝓝 (γ t₀)] 0) (t : T) :
    DirichletL.zagierSecondOrderODE (f t) =ᶠ[𝓝 (γ t)] 0 :=
  hf.zagierSecondOrderODE.eq_of_preconnectedSpace
    (.const hf.continuous (fun _ => analyticAt_const)) he t

theorem zagierConjugateAnalyticODE_eq_zero [PreconnectedSpace T]
    (hf : AnalyticContinuationAlong γ f) {t₀ : T}
    (he : DirichletL.zagierConjugateAnalyticODE (f t₀) =ᶠ[𝓝 (γ t₀)] 0) (t : T) :
    DirichletL.zagierConjugateAnalyticODE (f t) =ᶠ[𝓝 (γ t)] 0 :=
  hf.zagierConjugateAnalyticODE.eq_of_preconnectedSpace
    (.const hf.continuous (fun _ => analyticAt_const)) he t

end AnalyticContinuationAlong

theorem exists_zagierPathTransport_secondOrder_rep (b : zagierODERegularSet)
    {x y : ℂ} (δ : Path x y) (h₁ : ∀ t, δ t ≠ 1)
    (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1)
    (φ : zagierSolutionGerms (mobiusCoordinate x)) {f : ℂ → ℂ}
    (hE : zagierSecondOrderODE f =ᶠ[𝓝 x] 0)
    (hφ : mobiusGermPullback hx₁ (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g y ∧ zagierSecondOrderODE g =ᶠ[𝓝 y] 0 ∧
      mobiusGermPullback hy₁ (zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ :
        Germ (𝓝 (mobiusCoordinate y)) ℂ) = g := by
  obtain ⟨F, hF, hF₀, hF₁⟩ :=
    exists_analyticContinuationAlong_zagierMobiusPath b δ h₁ hreg hx₁ hy₁ φ hφ
  have he : zagierSecondOrderODE (F 0) =ᶠ[𝓝 (δ 0)] 0 := by
    simpa only [Path.source] using (eventuallyEq_zagierSecondOrderODE hF₀).trans hE
  exact ⟨F 1, by simpa only [Path.target] using hF.analytic 1,
    by simpa only [Path.target] using hF.zagierSecondOrderODE_eq_zero he 1, hF₁⟩

theorem exists_zagierPathTransport_conjugate_rep (b : zagierODERegularSet)
    {x y : ℂ} (δ : Path x y) (h₁ : ∀ t, δ t ≠ 1)
    (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1)
    (φ : zagierSolutionGerms (mobiusCoordinate x)) {f : ℂ → ℂ}
    (hC : zagierConjugateAnalyticODE f =ᶠ[𝓝 x] 0)
    (hφ : mobiusGermPullback hx₁ (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g y ∧ zagierConjugateAnalyticODE g =ᶠ[𝓝 y] 0 ∧
      mobiusGermPullback hy₁ (zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ :
        Germ (𝓝 (mobiusCoordinate y)) ℂ) = g := by
  obtain ⟨F, hF, hF₀, hF₁⟩ :=
    exists_analyticContinuationAlong_zagierMobiusPath b δ h₁ hreg hx₁ hy₁ φ hφ
  have he : zagierConjugateAnalyticODE (F 0) =ᶠ[𝓝 (δ 0)] 0 := by
    simpa only [Path.source] using (eventuallyEq_zagierConjugateAnalyticODE hF₀).trans hC
  exact ⟨F 1, by simpa only [Path.target] using hF.analytic 1,
    by simpa only [Path.target] using hF.zagierConjugateAnalyticODE_eq_zero he 1, hF₁⟩

end DirichletL
