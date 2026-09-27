import Analysis.ZagierPullbackAnalytic
import Analysis.ZagierSolutionGerms

/-!
Canonical complex-linear pullback of germs under CDT v2's coordinate `y in x`.
This compares the actual solution germs used in the monodromy step of `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- Composition with Y on full germs, away from the coordinate pole. -/
noncomputable def mobiusGermPullback {x : ℂ} (hx₁ : x ≠ 1) :
    Germ (𝓝 (mobiusCoordinate x)) ℂ →ₗ[ℂ] Germ (𝓝 x) ℂ where
  toFun φ := φ.compTendsto mobiusCoordinate (analyticAt_mobiusCoordinate hx₁).continuousAt
  map_add' φ ψ := Germ.inductionOn₂ φ ψ (fun _ _ => rfl)
  map_smul' _ φ := Germ.inductionOn φ (fun _ => rfl)

@[simp]
theorem mobiusGermPullback_coe {x : ℂ} (hx₁ : x ≠ 1) (f : ℂ → ℂ) :
    mobiusGermPullback hx₁ (f : Germ (𝓝 (mobiusCoordinate x)) ℂ) =
      (f ∘ mobiusCoordinate : ℂ → ℂ) := rfl

theorem mobiusGermPullback_injective {x : ℂ} (hx₀ : x ≠ 0) (hx₁ : x ≠ 1)
    (hx₂ : x ≠ 2) : Function.Injective (mobiusGermPullback hx₁) := by
  intro φ ψ
  induction φ, ψ using Germ.inductionOn₂ with
  | h f g =>
    intro he
    apply Germ.coe_eq.mpr
    exact eventuallyEq_of_comp_of_analyticAt (analyticAt_mobiusCoordinate hx₁)
      (deriv_mobiusCoordinate_ne_zero hx₀ hx₁ hx₂) (Germ.coe_eq.mp he)

theorem exists_zagierSolutionGerm_mobiusPullback {x : ℂ} (hx₀ : x ≠ 0)
    (hx₁ : x ≠ 1) (hx₂ : x ≠ 2) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f x)
    (hE : zagierSecondOrderODE f =ᶠ[𝓝 x] 0) :
    ∃ φ : zagierSolutionGerms (mobiusCoordinate x),
      mobiusGermPullback hx₁ (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f := by
  obtain ⟨g, hg, hgo, hgf⟩ := exists_zagierAnalyticODE_of_secondOrder hx₀ hx₁ hx₂ hf hE
  exact ⟨zagierSolutionGermOfFun g hg hgo, Germ.coe_eq.mpr hgf⟩

end DirichletL
