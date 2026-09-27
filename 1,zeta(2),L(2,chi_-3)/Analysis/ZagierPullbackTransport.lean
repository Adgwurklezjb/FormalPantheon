import Analysis.ZagierPullbackContinuation
import Analysis.ZagierContinuationTransport
import Analysis.MobiusGermPullback

/-!
Nontrivial closed second-order continuations give actual fourth-order
transport under CDT v2's coordinate `y in x`, for Lemma `14functions`.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

/-- The regular image of a complex path under the actual Mobius coordinate. -/
noncomputable def zagierMobiusPath {x y : ℂ} (δ : Path x y)
    (h₁ : ∀ t, δ t ≠ 1) (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet) :
    Path (⟨mobiusCoordinate x, by simpa only [Path.source] using hreg 0⟩ : zagierODERegularSet)
      ⟨mobiusCoordinate y, by simpa only [Path.target] using hreg 1⟩ where
  toFun t := ⟨mobiusCoordinate (δ t), hreg t⟩
  continuous_toFun := (continuous_iff_continuousAt.mpr (fun t =>
    (analyticAt_mobiusCoordinate (h₁ t)).continuousAt.comp δ.continuous.continuousAt)).subtype_mk _
  source' := Subtype.ext (congrArg mobiusCoordinate δ.source)
  target' := Subtype.ext (congrArg mobiusCoordinate δ.target)

@[simp]
theorem zagierMobiusPath_apply {x y : ℂ} (δ : Path x y)
    (h₁ : ∀ t, δ t ≠ 1) (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet) (t : I) :
    (zagierMobiusPath δ h₁ hreg t : ℂ) = mobiusCoordinate (δ t) := rfl

theorem zagierMobiusPath_symm {x y : ℂ} (δ : Path x y)
    (h₁ : ∀ t, δ t ≠ 1) (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet) :
    zagierMobiusPath δ.symm (fun t => h₁ (σ t)) (fun t => hreg (σ t)) =
      (zagierMobiusPath δ h₁ hreg).symm := by
  apply Path.ext
  rfl

theorem exists_analyticContinuationAlong_zagierMobiusPath (b : zagierODERegularSet)
    {x y : ℂ} (δ : Path x y) (h₁ : ∀ t, δ t ≠ 1)
    (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1)
    (φ : zagierSolutionGerms (mobiusCoordinate x)) {f : ℂ → ℂ}
    (hφ : mobiusGermPullback hx₁ (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f) :
    ∃ F : I → ℂ → ℂ, AnalyticContinuationAlong δ F ∧ F 0 =ᶠ[𝓝 x] f ∧
      mobiusGermPullback hy₁ (zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ :
        Germ (𝓝 (mobiusCoordinate y)) ℂ) = F 1 := by
  obtain ⟨g, hg, _, hg₀, hg₁⟩ := exists_analyticContinuationAlong_zagierPathTransport
    b (zagierMobiusPath δ h₁ hreg) φ
  refine ⟨fun t => g t ∘ mobiusCoordinate,
    hg.comp δ.continuous (fun t => analyticAt_mobiusCoordinate (h₁ t)) (fun _ => rfl),
    ?_, ?_⟩
  · exact Germ.coe_eq.mp ((congrArg (mobiusGermPullback hx₁) hg₀).trans hφ)
  · exact congrArg (mobiusGermPullback hy₁) hg₁.symm

theorem mobiusGermPullback_zagierPathTransport_of_analyticContinuation (b : zagierODERegularSet)
    {x y : ℂ} (δ : Path x y) (h₁ : ∀ t, δ t ≠ 1)
    (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1) {f : I → ℂ → ℂ}
    (hf : AnalyticContinuationAlong δ f) (φ : zagierSolutionGerms (mobiusCoordinate x))
    (hφ : mobiusGermPullback hx₁ (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f 0) :
    mobiusGermPullback hy₁ (zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ :
      Germ (𝓝 (mobiusCoordinate y)) ℂ) = f 1 := by
  obtain ⟨F, hF, hF₀, hF₁⟩ :=
    exists_analyticContinuationAlong_zagierMobiusPath b δ h₁ hreg hx₁ hy₁ φ hφ
  have hinit : F 0 =ᶠ[𝓝 (δ 0)] f 0 := by simpa only [Path.source] using hF₀
  have hend : F 1 =ᶠ[𝓝 y] f 1 := by
    simpa only [Path.target] using hF.eq_of_preconnectedSpace hf hinit 1
  exact hF₁.trans (Germ.coe_eq.mpr hend)

theorem mobiusGermPullback_zagierPathTransport (b : zagierODERegularSet)
    {x y : ℂ} (δ : Path x y) (h₁ : ∀ t, δ t ≠ 1)
    (hreg : ∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1) {f : I → ℂ → ℂ}
    (hf : AnalyticContinuationAlong δ f)
    (hE : ∀ t, zagierSecondOrderODE (f t) =ᶠ[𝓝 (δ t)] 0)
    (h₀ : ∀ t, δ t ≠ 0) (h₂ : ∀ t, δ t ≠ 2)
    (φ : zagierSolutionGerms (mobiusCoordinate x))
    (hφ : mobiusGermPullback hx₁ (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f 0) :
    mobiusGermPullback hy₁ (zagierPathTransport b (zagierMobiusPath δ h₁ hreg) φ :
      Germ (𝓝 (mobiusCoordinate y)) ℂ) = f 1 := by
  obtain ⟨g, hg, hgo, hgf⟩ :=
    exists_analyticContinuationAlong_zagierPullback hf hE h₀ h₁ h₂
  let γ := zagierMobiusPath δ h₁ hreg
  have hg' : AnalyticContinuationAlong (fun t => (γ t : ℂ)) g := hg
  let φ₀ : zagierSolutionGerms (mobiusCoordinate x) :=
    zagierSolutionGermsCongr γ.source (zagierSolutionGermOfFun (g 0) (hg'.analytic 0) (hgo 0))
  have hφ₀ : mobiusGermPullback hx₁ (φ₀ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f 0 := by
    rw [show (φ₀ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = g 0 from
      zagierSolutionGermsCongr_ofFun_coe γ.source _ _ _, mobiusGermPullback_coe]
    exact Germ.coe_eq.mpr (by simpa only [Path.source] using hgf 0)
  have he : φ = φ₀ := by
    apply Subtype.ext
    exact mobiusGermPullback_injective (by simpa only [Path.source] using h₀ 0) hx₁
      (by simpa only [Path.source] using h₂ 0) (hφ.trans hφ₀.symm)
  change mobiusGermPullback hy₁ (zagierPathTransport b γ φ :
    Germ (𝓝 (mobiusCoordinate y)) ℂ) = f 1
  rw [he, show φ₀ = zagierSolutionGermsCongr γ.source
    (zagierSolutionGermOfFun (g 0) (hg'.analytic 0) (hgo 0)) from rfl,
    zagierPathTransport_of_analyticContinuation b γ hg' hgo,
    zagierSolutionGermsCongr_ofFun_coe, mobiusGermPullback_coe]
  exact Germ.coe_eq.mpr (by simpa only [Path.target] using hgf 1)

theorem exists_zagierPathTransport_ne_of_secondOrder {b : zagierODERegularSet}
    (γ : Path b b) {x : ℂ} (δ : Path x x) {f : I → ℂ → ℂ}
    (hf : AnalyticContinuationAlong δ f)
    (hE : ∀ t, zagierSecondOrderODE (f t) =ᶠ[𝓝 (δ t)] 0)
    (h₀ : ∀ t, δ t ≠ 0) (h₁ : ∀ t, δ t ≠ 1) (h₂ : ∀ t, δ t ≠ 2)
    (hproj : ∀ t, mobiusCoordinate (δ t) = (γ t : ℂ))
    (hne : ¬f 0 =ᶠ[𝓝 x] f 1) :
    ∃ φ : zagierSolutionGerms (b : ℂ), zagierPathTransport b γ φ ≠ φ := by
  obtain ⟨g, hg, hgo, hgf⟩ :=
    exists_analyticContinuationAlong_zagierPullback hf hE h₀ h₁ h₂
  have hγ : mobiusCoordinate ∘ δ = fun t => (γ t : ℂ) := funext hproj
  rw [hγ] at hg
  have hgE : ∀ t, zagierAnalyticODE (g t) =ᶠ[𝓝 (γ t : ℂ)] 0 := by
    intro t
    simpa only [hproj t] using hgo t
  apply exists_zagierPathTransport_ne_of_analyticContinuation γ hg hgE
  intro he
  have hY : mobiusCoordinate x = (b : ℂ) := by
    simpa only [Path.source] using hproj 0
  have hYc : ContinuousAt mobiusCoordinate x :=
    (analyticAt_mobiusCoordinate (by simpa only [Path.source] using h₁ 0)).continuousAt
  have ht : Tendsto mobiusCoordinate (𝓝 x) (𝓝 (b : ℂ)) := by
    simpa only [hY] using hYc.tendsto
  have hg₀ : (g 0 ∘ mobiusCoordinate) =ᶠ[𝓝 x] f 0 := by
    simpa only [Path.source] using hgf 0
  have hg₁ : (g 1 ∘ mobiusCoordinate) =ᶠ[𝓝 x] f 1 := by
    simpa only [Path.target] using hgf 1
  exact hne (hg₀.symm.trans ((he.comp_tendsto ht).trans hg₁))

end DirichletL
