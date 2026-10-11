import Analysis.AnalyticLinearODEContinuationAtlas
import Analysis.AnalyticContinuation

/-!
Path continuation of actual solutions of finite analytic matrix equations.
The discrete solution-germ covering supplies the regular-locus continuation
needed for CDT v2, Lemma `14functions`.
-/

namespace DirichletL.AnalyticMatrixODE

open Filter Topology Bundle
open scoped Topology Matrix

variable {I : Type*} [Fintype I] (D : AnalyticMatrixODE I)

noncomputable instance instTopologicalSpaceContinuation (b : D.domain) :
    TopologicalSpace (D.Continuation b) := (D.continuationPrebundle b).totalSpaceTopology

noncomputable instance instFiberBundleContinuation (b : D.domain) :
    FiberBundle (D.solutionGerms (b : ℂ))
      (fun x : D.domain => D.solutionGerms (x : ℂ)) :=
  (D.continuationPrebundle b).toFiberBundle

namespace SolutionFrame

variable {D}

/-- A frame gives a genuine trivialization of the solution-germ covering. -/
noncomputable def trivialization (e : D.SolutionFrame) (b : D.domain) :
    Trivialization (D.solutionGerms (b : ℂ)) (D.continuationProjection b) :=
  (D.continuationPrebundle b).trivializationOfMemPretrivializationAtlas
    (e := e.pretrivialization b) ⟨e, rfl⟩

@[simp]
theorem trivialization_baseSet (e : D.SolutionFrame) (b : D.domain) :
    (e.trivialization b).baseSet = e.baseSet := rfl

@[simp]
theorem trivialization_apply (e : D.SolutionFrame) (b : D.domain) (p : D.Continuation b) :
    e.trivialization b p = (p.proj, e.coordinates b p.proj p.snd) := rfl

@[simp]
theorem trivialization_symm_apply (e : D.SolutionFrame) (b : D.domain)
    (q : D.domain × D.solutionGerms (b : ℂ)) :
    (e.trivialization b).toPartialEquiv.symm q =
      ⟨q.1, e.fromCoordinates b q.1 q.2⟩ := rfl

end SolutionFrame

theorem eventually_continuation_eq_fromCoordinates (b : D.domain)
    {T : Type*} [TopologicalSpace T] {u : T → D.Continuation b} {t : T}
    (hu : ContinuousAt u t) :
    ∃ e : D.SolutionFrame, (u t).proj ∈ e.baseSet ∧
      ∃ c : D.solutionGerms (b : ℂ), ∀ᶠ s in 𝓝 t,
        (u s).proj ∈ e.baseSet ∧
          u s = ⟨(u s).proj, e.fromCoordinates b (u s).proj c⟩ := by
  let e := SolutionFrame.atPoint (u t).proj
  have ht : (u t).proj ∈ e.baseSet := SolutionFrame.mem_baseSet_atPoint _
  let q := e.trivialization b
  have hsource : u t ∈ q.source := q.mem_source.mpr ht
  have hnear : ∀ᶠ s in 𝓝 t, u s ∈ q.source :=
    hu.eventually (q.open_source.mem_nhds hsource)
  have hc : ContinuousAt (fun s => (q (u s)).2) t :=
    continuous_snd.continuousAt.comp
      ((q.continuousOn.continuousAt (q.open_source.mem_nhds hsource)).comp hu)
  have heq : ∀ᶠ s in 𝓝 t, (q (u s)).2 = (q (u t)).2 :=
    hc.eventually ((isOpen_discrete {(q (u t)).2}).mem_nhds rfl)
  refine ⟨e, ht, (q (u t)).2, ?_⟩
  filter_upwards [hnear, heq] with s hs he
  have hm : (u s).proj ∈ e.baseSet := q.mem_source.mp hs
  refine ⟨hm, ?_⟩
  change e.coordinates b (u s).proj (u s).snd = (q (u t)).2 at he
  rw [← he, e.fromCoordinates_coordinates b (u s).proj hm]

/-- Continuous germs locally have a common actual analytic vector representative. -/
theorem exists_continuation_local_representative (b : D.domain)
    {T : Type*} [TopologicalSpace T] {u : T → D.Continuation b} {t : T}
    (hu : ContinuousAt u t) :
    ∃ e : D.SolutionFrame, (u t).proj ∈ e.baseSet ∧
      ∃ f : ℂ → I → ℂ, AnalyticOnNhd ℂ f (Metric.ball e.center e.radius) ∧
        (∀ z ∈ Metric.ball e.center e.radius, HasDerivAt f (D.matrix z *ᵥ f z) z) ∧
        ∀ᶠ s in 𝓝 t, (u s).proj ∈ e.baseSet ∧
          ((u s).snd : Germ (𝓝 ((u s).proj : ℂ)) (I → ℂ)) = f := by
  obtain ⟨e, ht, c, hc⟩ := D.eventually_continuation_eq_fromCoordinates b hu
  refine ⟨e, ht, e.vectorSection b c, e.analyticOnNhd_vectorSection b c,
    fun z hz => e.ode_vectorSection b c hz, ?_⟩
  filter_upwards [hc] with s hs
  refine ⟨hs.1, ?_⟩
  have he : (u s).snd = e.fromCoordinates b (u s).proj c :=
    Bundle.TotalSpace.mk_injective (u s).proj hs.2
  rw [he]
  exact e.fromCoordinates_eq_vectorSection_germ b (u s).proj hs.1 c

/-- The vector solution-germ projection is a covering of the analytic domain. -/
theorem isCoveringMap_continuationProjection (b : D.domain) :
    IsCoveringMap (D.continuationProjection b) := FiberBundle.isCoveringMap

theorem continuous_continuationProjection (b : D.domain) :
    Continuous (D.continuationProjection b) :=
  (D.isCoveringMap_continuationProjection b).continuous

theorem analyticContinuationAlong_component (b : D.domain)
    {T : Type*} [TopologicalSpace T] {u : T → D.Continuation b} {f : T → ℂ → I → ℂ}
    (hu : Continuous u)
    (hrep : ∀ t, ((u t).snd : Germ (𝓝 ((u t).proj : ℂ)) (I → ℂ)) = f t) (i : I) :
    AnalyticContinuationAlong (fun t => ((u t).proj : ℂ)) (fun t z => f t z i) := by
  have hγ : Continuous (fun t => ((u t).proj : ℂ)) :=
    continuous_subtype_val.comp ((D.continuous_continuationProjection b).comp hu)
  refine ⟨hγ, ?_, ?_⟩
  · intro t
    apply analyticAt_pi_iff.mp ((D.mem_solutionGerms_iff.mp ?_).1) i
    rw [← hrep t]
    exact (u t).snd.property
  · intro t
    obtain ⟨e, _, g, _, _, hnear⟩ := D.exists_continuation_local_representative b hu.continuousAt
    have he : f t =ᶠ[𝓝 ((u t).proj : ℂ)] g :=
      Germ.coe_eq.mp ((hrep t).symm.trans hnear.self_of_nhds.2)
    have hn := hγ.continuousAt.tendsto.eventually he.eventually_nhds
    filter_upwards [hnear, hn] with s hs hns
    have hfg := (Germ.coe_eq.mp ((hrep s).symm.trans hs.2)).trans (Filter.EventuallyEq.symm hns)
    filter_upwards [hfg] with z hz
    exact congrFun hz i

/-- Every local analytic vector solution continues along every path in the domain. -/
theorem exists_analyticContinuationAlong (γ : C(unitInterval, D.domain)) (f : ℂ → I → ℂ)
    (hf : AnalyticAt ℂ f (γ 0 : ℂ))
    (hfo : ∀ᶠ z in 𝓝 (γ 0 : ℂ), HasDerivAt f (D.matrix z *ᵥ f z) z) :
    ∃ F : unitInterval → ℂ → I → ℂ,
      (∀ i, AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun t z => F t z i)) ∧
      F 0 =ᶠ[𝓝 (γ 0 : ℂ)] f ∧
      ∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), HasDerivAt (F t) (D.matrix z *ᵥ F t z) z := by
  let p : D.Continuation (γ 0) := ⟨γ 0, D.solutionGermOfFun f hf hfo⟩
  let hcover := D.isCoveringMap_continuationProjection (γ 0)
  let u := hcover.liftPath γ p rfl
  have hp : ∀ t, (u t).proj = γ t := fun t => congrFun (hcover.liftPath_lifts γ p rfl) t
  have hzero : u 0 = p := hcover.liftPath_zero γ p rfl
  choose F hFa hFo hFg using (fun t => (u t).snd.property)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    simpa only [hp] using
      D.analyticContinuationAlong_component (γ 0) u.continuous (fun t => (hFg t).symm) i
  · have he := hFg 0
    rw [hzero] at he
    exact Germ.coe_eq.mp he
  · intro t
    simpa only [hp] using hFo t

end DirichletL.AnalyticMatrixODE
