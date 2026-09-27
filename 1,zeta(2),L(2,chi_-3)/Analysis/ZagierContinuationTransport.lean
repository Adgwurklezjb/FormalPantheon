import Analysis.ZagierContinuationRepresentatives
import Analysis.ZagierPathTransport

/-!
Compatible analytic representatives compute the actual path transport used
in the monodromy step of CDT v2, Lemma `14functions`.
-/

namespace DirichletL

open Filter Bundle unitInterval
open scoped Topology

theorem zagierSolutionGermsCongr_ofFun_coe {x y : zagierODERegularSet} (h : x = y)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f (x : ℂ))
    (hfo : zagierAnalyticODE f =ᶠ[𝓝 (x : ℂ)] 0) :
    (zagierSolutionGermsCongr h (zagierSolutionGermOfFun f hf hfo) :
      Germ (𝓝 (y : ℂ)) ℂ) = f := by
  subst y
  rfl

theorem exists_analyticContinuationAlong_zagierPathTransport (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y)
    (φ : zagierSolutionGerms (x : ℂ)) :
    ∃ f : I → ℂ → ℂ, AnalyticContinuationAlong (fun t => (γ t : ℂ)) f ∧
      (∀ t, zagierAnalyticODE (f t) =ᶠ[𝓝 (γ t : ℂ)] 0) ∧
      (f 0 : Germ (𝓝 (x : ℂ)) ℂ) = φ ∧
      (f 1 : Germ (𝓝 (y : ℂ)) ℂ) = zagierPathTransport b γ φ := by
  choose f hf hfo hrep using fun t => (zagierPathGerm b γ φ t).property
  have hc : AnalyticContinuationAlong (fun t => (γ t : ℂ)) f :=
    analyticContinuationAlong_of_continuous_zagierContinuation b
      (continuous_zagierPathGerm b γ φ) (fun t => (hrep t).symm)
  have hpack (t : I) : zagierSolutionGermOfFun (f t) (hf t) (hfo t) =
      zagierPathGerm b γ φ t := Subtype.ext (hrep t)
  have hzero : zagierSolutionGermsCongr γ.source
      (zagierSolutionGermOfFun (f 0) (hf 0) (hfo 0)) = φ := by
    apply Bundle.TotalSpace.mk_injective (F := zagierSolutionGerms (b : ℂ))
      (E := fun z : zagierODERegularSet => zagierSolutionGerms (z : ℂ)) x
    rw [mk_zagierSolutionGermsCongr, hpack, mk_zagierPathGerm, zagierPathLift_zero]
  refine ⟨f, hc, hfo, ?_, ?_⟩
  · have he := congrArg (fun u : zagierSolutionGerms (x : ℂ) =>
      (u : Germ (𝓝 (x : ℂ)) ℂ)) hzero
    simpa only [zagierSolutionGermsCongr_ofFun_coe] using he
  · rw [zagierPathTransport, ← hpack 1, zagierSolutionGermsCongr_ofFun_coe]

theorem zagierPathTransport_of_analyticContinuation (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y) {f : I → ℂ → ℂ}
    (hf : AnalyticContinuationAlong (fun t => (γ t : ℂ)) f)
    (hE : ∀ t, zagierAnalyticODE (f t) =ᶠ[𝓝 (γ t : ℂ)] 0) :
    zagierPathTransport b γ (zagierSolutionGermsCongr γ.source
      (zagierSolutionGermOfFun (f 0) (hf.analytic 0) (hE 0))) =
        zagierSolutionGermsCongr γ.target
          (zagierSolutionGermOfFun (f 1) (hf.analytic 1) (hE 1)) := by
  let u : I → ZagierContinuation b := fun t =>
    ⟨γ t, zagierSolutionGermOfFun (f t) (hf.analytic t) (hE t)⟩
  have hu : Continuous u :=
    continuous_zagierContinuation_of_analyticContinuation b hf (fun _ => rfl)
  let Γ : Path
      (⟨x, zagierSolutionGermsCongr γ.source
        (zagierSolutionGermOfFun (f 0) (hf.analytic 0) (hE 0))⟩ : ZagierContinuation b)
      ⟨y, zagierSolutionGermsCongr γ.target
        (zagierSolutionGermOfFun (f 1) (hf.analytic 1) (hE 1))⟩ := {
    toContinuousMap := ⟨u, hu⟩
    source' := (mk_zagierSolutionGermsCongr b γ.source _).symm
    target' := (mk_zagierSolutionGermsCongr b γ.target _).symm }
  apply zagierPathTransport_eq_of_lift b γ _ _ Γ
  apply Path.ext
  rfl

theorem exists_zagierPathTransport_ne_of_analyticContinuation {b : zagierODERegularSet}
    (γ : Path b b) {f : I → ℂ → ℂ}
    (hf : AnalyticContinuationAlong (fun t => (γ t : ℂ)) f)
    (hE : ∀ t, zagierAnalyticODE (f t) =ᶠ[𝓝 (γ t : ℂ)] 0)
    (hne : ¬f 0 =ᶠ[𝓝 (b : ℂ)] f 1) :
    ∃ φ : zagierSolutionGerms (b : ℂ), zagierPathTransport b γ φ ≠ φ := by
  refine ⟨zagierSolutionGermsCongr γ.source
    (zagierSolutionGermOfFun (f 0) (hf.analytic 0) (hE 0)), ?_⟩
  intro he
  rw [zagierPathTransport_of_analyticContinuation b γ hf hE] at he
  have he' := congrArg (fun φ : zagierSolutionGerms (b : ℂ) => (φ : Germ (𝓝 (b : ℂ)) ℂ)) he
  simp only [zagierSolutionGermsCongr_ofFun_coe] at he'
  exact hne (Germ.coe_eq.mp he'.symm)

end DirichletL
