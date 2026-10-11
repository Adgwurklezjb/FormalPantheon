import Analysis.AnalyticLinearODEContinuation

/-!
Common full representatives determine continuous matrix-solution sections.
Source: CDT v2 TeX 1739-1744. Prior meanings and source/API checks are in
-/

namespace DirichletL.AnalyticMatrixODE

open Filter Bundle
open scoped Topology

variable {I : Type*} [Fintype I] {D : AnalyticMatrixODE I}

namespace SolutionFrame

theorem continuousOn_fromCoordinates (e : D.SolutionFrame) (b : D.domain)
    (c : D.solutionGerms (b : ℂ)) :
    ContinuousOn (fun x : D.domain =>
      (⟨x, e.fromCoordinates b x c⟩ : D.Continuation b)) e.baseSet := by
  change ContinuousOn
    (fun x : D.domain => (e.trivialization b).toPartialEquiv.symm (x, c)) e.baseSet
  exact (e.trivialization b).continuousOn_invFun.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, Set.mem_univ _⟩)

end SolutionFrame

variable (D)

theorem continuous_continuation_of_representative (b : D.domain)
    {T : Type*} [TopologicalSpace T] {u : T → D.Continuation b}
    {f : ℂ → I → ℂ} (hp : Continuous (fun t => (u t).proj))
    (hrep : ∀ t, ((u t).snd : Germ (𝓝 ((u t).proj : ℂ)) (I → ℂ)) = f) :
    Continuous u := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let e := SolutionFrame.atPoint (u t).proj
  have ht : (u t).proj ∈ e.baseSet := SolutionFrame.mem_baseSet_atPoint _
  let c := e.coordinates b (u t).proj (u t).snd
  have he : f =ᶠ[𝓝 ((u t).proj : ℂ)] e.vectorSection b c := by
    have h := e.fromCoordinates_eq_vectorSection_germ b (u t).proj ht c
    dsimp only [c] at h
    rw [e.fromCoordinates_coordinates b (u t).proj ht, hrep t] at h
    exact Germ.coe_eq.mp h
  have hc : ContinuousAt (fun s =>
      (⟨(u s).proj, e.fromCoordinates b (u s).proj c⟩ : D.Continuation b)) t :=
    ((e.continuousOn_fromCoordinates b c).continuousAt
      (e.isOpen_baseSet.mem_nhds ht)).comp (x := t) hp.continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [hp.continuousAt.preimage_mem_nhds (e.isOpen_baseSet.mem_nhds ht),
    (continuous_subtype_val.comp hp).continuousAt.tendsto.eventually he.eventually_nhds]
    with s hs hgs
  have hφ : (u s).snd = e.fromCoordinates b (u s).proj c := by
    apply Subtype.ext
    rw [hrep s, e.fromCoordinates_eq_vectorSection_germ b (u s).proj hs c]
    exact Germ.coe_eq.mpr hgs
  exact congrArg (Bundle.TotalSpace.mk (u s).proj) hφ

end DirichletL.AnalyticMatrixODE
