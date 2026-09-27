import Analysis.ZagierAnalyticConjugacy
import Analysis.ZagierSheetPaths
import Analysis.ZagierSummandTransport
import Analysis.ZagierMonodromy

/-!
Actual monodromy exchanging the two sheets in CDT v2, `y in x` and `14functions`.
The source and conjugate summands are exchanged at the same fourth-order base.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

/-- The regular projection of a path joining the two points over one y-base. -/
noncomputable def zagierSheetLoop {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet)
    (δ : Path x (mobiusAnalyticInvolution x)) (h₁ : ∀ t, δ t ≠ 1)
    (hδ : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet) :
    Path (⟨mobiusCoordinate x, hreg⟩ : zagierODERegularSet) ⟨mobiusCoordinate x, hreg⟩ where
  toFun t := ⟨mobiusCoordinate (δ t), hδ t⟩
  continuous_toFun := (continuous_iff_continuousAt.mpr (fun t =>
    (analyticAt_mobiusCoordinate (h₁ t)).continuousAt.comp δ.continuous.continuousAt)).subtype_mk _
  source' := Subtype.ext (congrArg mobiusCoordinate δ.source)
  target' := Subtype.ext ((congrArg mobiusCoordinate δ.target).trans
    (mobiusCoordinate_mobiusAnalyticInvolution hx))

@[simp]
theorem zagierSheetLoop_apply {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet)
    (δ : Path x (mobiusAnalyticInvolution x)) (h₁ : ∀ t, δ t ≠ 1)
    (hδ : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet) (t : I) :
    (zagierSheetLoop hx hreg δ h₁ hδ t : ℂ) = mobiusCoordinate (δ t) := rfl

theorem exists_analyticContinuationAlong_zagierSheetLoop {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet)
    (γ : Path (⟨mobiusCoordinate x, hreg⟩ : zagierODERegularSet) ⟨mobiusCoordinate x, hreg⟩)
    (δ : Path x (mobiusAnalyticInvolution x)) (h₁ : ∀ t, δ t ≠ 1)
    (hproj : ∀ t, mobiusCoordinate (δ t) = (γ t : ℂ))
    (φ : zagierSolutionGerms (mobiusCoordinate x)) {f : ℂ → ℂ}
    (hφ : mobiusGermPullback hx (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f) :
    ∃ F : I → ℂ → ℂ, AnalyticContinuationAlong δ F ∧ F 0 =ᶠ[𝓝 x] f ∧
      mobiusGermPullback hx (zagierPathTransport ⟨mobiusCoordinate x, hreg⟩ γ φ :
        Germ (𝓝 (mobiusCoordinate x)) ℂ) = (F 1 ∘ mobiusAnalyticInvolution : ℂ → ℂ) := by
  obtain ⟨g, hg, _, hg₀, hg₁⟩ := exists_analyticContinuationAlong_zagierPathTransport
    ⟨mobiusCoordinate x, hreg⟩ γ φ
  refine ⟨fun t => g t ∘ mobiusCoordinate,
    hg.comp δ.continuous (fun t => analyticAt_mobiusCoordinate (h₁ t)) hproj, ?_, ?_⟩
  · exact Germ.coe_eq.mp ((congrArg (mobiusGermPullback hx) hg₀).trans hφ)
  · rw [← hg₁, mobiusGermPullback_coe]
    apply Germ.coe_eq.mpr
    filter_upwards [eventually_ne_nhds hx] with z hz
    exact congrArg (g 1) (mobiusCoordinate_mobiusAnalyticInvolution hz).symm

theorem zagierPathTransport_sheet_mem_conjugateSummand {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet)
    (γ : Path (⟨mobiusCoordinate x, hreg⟩ : zagierODERegularSet) ⟨mobiusCoordinate x, hreg⟩)
    (δ : Path x (mobiusAnalyticInvolution x)) (h₁ : ∀ t, δ t ≠ 1)
    (hproj : ∀ t, mobiusCoordinate (δ t) = (γ t : ℂ))
    {φ : zagierSolutionGerms (mobiusCoordinate x)} (hφ : φ ∈ zagierSourceSummand hx) :
    zagierPathTransport ⟨mobiusCoordinate x, hreg⟩ γ φ ∈ zagierConjugateSummand hx := by
  obtain ⟨f, _, hE, hf⟩ := hφ
  obtain ⟨F, hF, hF₀, hF₁⟩ :=
    exists_analyticContinuationAlong_zagierSheetLoop hx hreg γ δ h₁ hproj φ hf
  have he : zagierSecondOrderODE (F 0) =ᶠ[𝓝 (δ 0)] 0 := by
    simpa only [Path.source] using (eventuallyEq_zagierSecondOrderODE hF₀).trans hE
  have ha : AnalyticAt ℂ (F 1) (mobiusAnalyticInvolution x) := by
    simpa only [Path.target] using hF.analytic 1
  have he₁ : zagierSecondOrderODE (F 1) =ᶠ[𝓝 (mobiusAnalyticInvolution x)] 0 := by
    simpa only [Path.target] using hF.zagierSecondOrderODE_eq_zero he 1
  exact ⟨F 1 ∘ mobiusAnalyticInvolution, ha.comp (analyticAt_mobiusAnalyticInvolution hx),
    eventually_zagierConjugate_comp_mobiusAnalyticInvolution hx ha he₁, hF₁⟩

theorem zagierPathTransport_sheet_mem_sourceSummand {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet)
    (γ : Path (⟨mobiusCoordinate x, hreg⟩ : zagierODERegularSet) ⟨mobiusCoordinate x, hreg⟩)
    (δ : Path x (mobiusAnalyticInvolution x)) (h₁ : ∀ t, δ t ≠ 1)
    (hproj : ∀ t, mobiusCoordinate (δ t) = (γ t : ℂ))
    {φ : zagierSolutionGerms (mobiusCoordinate x)} (hφ : φ ∈ zagierConjugateSummand hx) :
    zagierPathTransport ⟨mobiusCoordinate x, hreg⟩ γ φ ∈ zagierSourceSummand hx := by
  obtain ⟨f, _, hC, hf⟩ := hφ
  obtain ⟨F, hF, hF₀, hF₁⟩ :=
    exists_analyticContinuationAlong_zagierSheetLoop hx hreg γ δ h₁ hproj φ hf
  have he : zagierConjugateAnalyticODE (F 0) =ᶠ[𝓝 (δ 0)] 0 := by
    simpa only [Path.source] using (eventuallyEq_zagierConjugateAnalyticODE hF₀).trans hC
  have ha : AnalyticAt ℂ (F 1) (mobiusAnalyticInvolution x) := by
    simpa only [Path.target] using hF.analytic 1
  have he₁ : zagierConjugateAnalyticODE (F 1) =ᶠ[𝓝 (mobiusAnalyticInvolution x)] 0 := by
    simpa only [Path.target] using hF.zagierConjugateAnalyticODE_eq_zero he 1
  exact ⟨F 1 ∘ mobiusAnalyticInvolution, ha.comp (analyticAt_mobiusAnalyticInvolution hx),
    eventually_zagierSecondOrder_comp_mobiusAnalyticInvolution hx ha he₁, hF₁⟩

private theorem mem_right_iff_of_isCompl_swap {V : Type*} [AddCommGroup V] [Module ℂ V]
    (e : V ≃ₗ[ℂ] V) {P Q : Submodule ℂ V} (hPQ : IsCompl P Q)
    (hP : ∀ v ∈ P, e v ∈ Q) (hQ : ∀ v ∈ Q, e v ∈ P) (v : V) : e v ∈ Q ↔ v ∈ P := by
  constructor
  · intro hv
    have hsup : v ∈ P ⊔ Q := by rw [hPQ.sup_eq_top]; trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hsup
    have hq' : e q ∈ Q := by
      simpa only [map_add, add_sub_cancel_left] using Q.sub_mem hv (hP p hp)
    have heq := Submodule.disjoint_def.mp hPQ.disjoint (e q) (hQ q hq) hq'
    have hzero : q = 0 := e.injective (by simpa only [map_zero] using heq)
    simpa only [hzero, add_zero] using hp
  · exact hP v

theorem exists_zagierSheetExchange_monodromy {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet) :
    let b : zagierODERegularSet := ⟨mobiusCoordinate x, hreg⟩
    ∃ g : FundamentalGroup zagierODERegularSet b,
      ∀ φ : zagierSolutionGerms (mobiusCoordinate x),
        (zagierMonodromyRepresentation b g φ ∈ zagierConjugateSummand hx ↔
          φ ∈ zagierSourceSummand hx) ∧
        (zagierMonodromyRepresentation b g φ ∈ zagierSourceSummand hx ↔
          φ ∈ zagierConjugateSummand hx) := by
  let b : zagierODERegularSet := ⟨mobiusCoordinate x, hreg⟩
  obtain ⟨δ, h₁, hδ⟩ := exists_zagierSheetPath hx hreg
  let γ := zagierSheetLoop hx hreg δ h₁ hδ
  have hP (φ : zagierSolutionGerms (mobiusCoordinate x)) (hφ : φ ∈ zagierSourceSummand hx) :
      zagierPathTransportEquiv b γ φ ∈ zagierConjugateSummand hx :=
    zagierPathTransport_sheet_mem_conjugateSummand hx hreg γ δ h₁ (fun _ => rfl) hφ
  have hQ (φ : zagierSolutionGerms (mobiusCoordinate x)) (hφ : φ ∈ zagierConjugateSummand hx) :
      zagierPathTransportEquiv b γ φ ∈ zagierSourceSummand hx :=
    zagierPathTransport_sheet_mem_sourceSummand hx hreg γ δ h₁ (fun _ => rfl) hφ
  refine ⟨FundamentalGroup.fromPath (X := TopCat.of zagierODERegularSet) ⟦γ⟧, fun φ => ⟨?_, ?_⟩⟩
  · exact mem_right_iff_of_isCompl_swap (zagierPathTransportEquiv b γ)
      (isCompl_zagierSolutionSummands hx hreg) hP hQ φ
  · exact mem_right_iff_of_isCompl_swap (zagierPathTransportEquiv b γ)
      (isCompl_zagierSolutionSummands hx hreg).symm hQ hP φ

end DirichletL
