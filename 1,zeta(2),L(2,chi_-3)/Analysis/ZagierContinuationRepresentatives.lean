import Analysis.AnalyticContinuation
import Analysis.ZagierContinuation

/-!
Compatible local analytic representatives give continuous paths in the
existing fourth-order continuation covering used in CDT v2, `14functions`.
-/

namespace DirichletL

open Filter Bundle
open scoped Topology

theorem analyticContinuationAlong_of_continuous_zagierContinuation (b : zagierODERegularSet)
    {T : Type*} [TopologicalSpace T] {u : T → ZagierContinuation b} {f : T → ℂ → ℂ}
    (hu : Continuous u)
    (hrep : ∀ t, ((u t).snd : Germ (𝓝 ((u t).proj : ℂ)) ℂ) = f t) :
    AnalyticContinuationAlong (fun t => ((u t).proj : ℂ)) f := by
  have hγ : Continuous (fun t => ((u t).proj : ℂ)) :=
    continuous_subtype_val.comp ((continuous_zagierContinuationProjection b).comp hu)
  refine ⟨hγ, ?_, ?_⟩
  · intro t
    apply (mem_zagierSolutionGerms_iff.mp ?_).1
    rw [← hrep t]
    exact (u t).snd.property
  · intro t
    obtain ⟨e, _, g, _, _, hnear⟩ :=
      exists_zagierContinuation_local_representative b hu.continuousAt
    have he : f t =ᶠ[𝓝 ((u t).proj : ℂ)] g :=
      Germ.coe_eq.mp ((hrep t).symm.trans hnear.self_of_nhds.2)
    have hn := hγ.continuousAt.tendsto.eventually he.eventually_nhds
    filter_upwards [hnear, hn] with s hs hns
    exact (Germ.coe_eq.mp ((hrep s).symm.trans hs.2)).trans (Filter.EventuallyEq.symm hns)

theorem continuous_zagierContinuation_of_analyticContinuation (b : zagierODERegularSet)
    {T : Type*} [TopologicalSpace T] {u : T → ZagierContinuation b} {f : T → ℂ → ℂ}
    (hf : AnalyticContinuationAlong (fun t => ((u t).proj : ℂ)) f)
    (hrep : ∀ t, ((u t).snd : Germ (𝓝 ((u t).proj : ℂ)) ℂ) = f t) : Continuous u := by
  have hp : Continuous (fun t => (u t).proj) :=
    hf.continuous.subtype_mk (fun t => (u t).proj.property)
  apply continuous_iff_continuousAt.mpr
  intro t
  let e := ZagierSolutionFrame.atPoint (u t).proj
  have ht : (u t).proj ∈ e.baseSet := ZagierSolutionFrame.mem_baseSet_atPoint _
  let c := e.coordinates b (u t).proj (u t).snd
  have he : f t =ᶠ[𝓝 ((u t).proj : ℂ)] e.scalarSection b c := by
    have h := e.fromCoordinates_eq_scalarSection_germ b (u t).proj ht c
    dsimp only [c] at h
    rw [e.fromCoordinates_coordinates b (u t).proj ht, hrep t] at h
    exact Germ.coe_eq.mp h
  have hc : ContinuousAt (fun s =>
      (⟨(u s).proj, e.fromCoordinates b (u s).proj c⟩ : ZagierContinuation b)) t :=
    ((e.continuousOn_fromCoordinates b c).continuousAt
      (e.isOpen_baseSet.mem_nhds ht)).comp (x := t) hp.continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [hp.continuousAt.preimage_mem_nhds (e.isOpen_baseSet.mem_nhds ht),
    hf.locally_eq t, hf.continuous.continuousAt.tendsto.eventually he.eventually_nhds]
    with s hs hfs hgs
  have hφ : (u s).snd = e.fromCoordinates b (u s).proj c := by
    apply Subtype.ext
    rw [hrep s, e.fromCoordinates_eq_scalarSection_germ b (u s).proj hs c]
    exact Germ.coe_eq.mpr (hfs.trans hgs)
  exact congrArg (Bundle.TotalSpace.mk (u s).proj) hφ

end DirichletL
