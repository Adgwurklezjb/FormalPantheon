import Analysis.ZagierContinuationAtlas

/-!
The covering of homogeneous Zagier solution germs and its path lifts.
This establishes regular-locus continuation used in CDT v2, Lemma `14functions`;
monodromy irreducibility and removal of the extra cubic singularities remain separate.
-/

namespace DirichletL

open Filter Topology Bundle unitInterval
open scoped Topology

noncomputable instance instTopologicalSpaceZagierContinuation (b : zagierODERegularSet) :
    TopologicalSpace (ZagierContinuation b) :=
  (zagierContinuationPrebundle b).totalSpaceTopology

noncomputable instance instFiberBundleZagierContinuation (b : zagierODERegularSet) :
    FiberBundle (zagierSolutionGerms (b : ℂ))
      (fun x : zagierODERegularSet => zagierSolutionGerms (x : ℂ)) :=
  (zagierContinuationPrebundle b).toFiberBundle

namespace ZagierSolutionFrame

/-- A solution frame gives a genuine trivialization of the continuation covering. -/
noncomputable def trivialization (e : ZagierSolutionFrame) (b : zagierODERegularSet) :
    Trivialization (zagierSolutionGerms (b : ℂ)) (zagierContinuationProjection b) :=
  (zagierContinuationPrebundle b).trivializationOfMemPretrivializationAtlas
    (e := e.pretrivialization b) ⟨e, rfl⟩

@[simp]
theorem trivialization_baseSet (e : ZagierSolutionFrame) (b : zagierODERegularSet) :
    (e.trivialization b).baseSet = e.baseSet := rfl

@[simp]
theorem trivialization_apply (e : ZagierSolutionFrame) (b : zagierODERegularSet)
    (p : ZagierContinuation b) :
    e.trivialization b p = (p.proj, e.coordinates b p.proj p.snd) := rfl

@[simp]
theorem trivialization_symm_apply (e : ZagierSolutionFrame) (b : zagierODERegularSet)
    (q : zagierODERegularSet × zagierSolutionGerms (b : ℂ)) :
    (e.trivialization b).toPartialEquiv.symm q =
      ⟨q.1, e.fromCoordinates b q.1 q.2⟩ := rfl

theorem continuousOn_fromCoordinates (e : ZagierSolutionFrame) (b : zagierODERegularSet)
    (c : zagierSolutionGerms (b : ℂ)) :
    ContinuousOn (fun x : zagierODERegularSet =>
      (⟨x, e.fromCoordinates b x c⟩ : ZagierContinuation b)) e.baseSet := by
  change ContinuousOn
    (fun x : zagierODERegularSet => (e.trivialization b).toPartialEquiv.symm (x, c)) e.baseSet
  exact (e.trivialization b).continuousOn_invFun.comp
    (continuous_id.prodMk continuous_const).continuousOn (fun x hx => ⟨hx, Set.mem_univ _⟩)

end ZagierSolutionFrame

theorem eventually_zagierContinuation_eq_fromCoordinates (b : zagierODERegularSet)
    {T : Type*} [TopologicalSpace T] {u : T → ZagierContinuation b} {t : T}
    (hu : ContinuousAt u t) :
    ∃ e : ZagierSolutionFrame, (u t).proj ∈ e.baseSet ∧
      ∃ c : zagierSolutionGerms (b : ℂ), ∀ᶠ s in 𝓝 t,
        (u s).proj ∈ e.baseSet ∧
          u s = ⟨(u s).proj, e.fromCoordinates b (u s).proj c⟩ := by
  let e := ZagierSolutionFrame.atPoint (u t).proj
  have ht : (u t).proj ∈ e.baseSet := ZagierSolutionFrame.mem_baseSet_atPoint _
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

/-- Continuous continuation germs locally come from one actual analytic scalar solution. -/
theorem exists_zagierContinuation_local_representative (b : zagierODERegularSet)
    {T : Type*} [TopologicalSpace T] {u : T → ZagierContinuation b} {t : T}
    (hu : ContinuousAt u t) :
    ∃ e : ZagierSolutionFrame, (u t).proj ∈ e.baseSet ∧
      ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Metric.ball e.center e.radius) ∧
        Set.EqOn (zagierAnalyticODE f) 0 (Metric.ball e.center e.radius) ∧
        ∀ᶠ s in 𝓝 t, (u s).proj ∈ e.baseSet ∧
          ((u s).snd : Germ (𝓝 ((u s).proj : ℂ)) ℂ) = f := by
  obtain ⟨e, ht, c, hc⟩ := eventually_zagierContinuation_eq_fromCoordinates b hu
  refine ⟨e, ht, e.scalarSection b c, e.analyticOnNhd_scalarSection b c,
    e.ode_scalarSection b c, ?_⟩
  filter_upwards [hc] with s hs
  refine ⟨hs.1, ?_⟩
  have he : (u s).snd = e.fromCoordinates b (u s).proj c :=
    Bundle.TotalSpace.mk_injective (u s).proj hs.2
  rw [he]
  exact e.fromCoordinates_eq_scalarSection_germ b (u s).proj hs.1 c

/-- The actual solution-germ projection is a covering on the regular locus. -/
theorem isCoveringMap_zagierContinuationProjection (b : zagierODERegularSet) :
    IsCoveringMap (zagierContinuationProjection b) := FiberBundle.isCoveringMap

theorem continuous_zagierContinuationProjection (b : zagierODERegularSet) :
    Continuous (zagierContinuationProjection b) :=
  (isCoveringMap_zagierContinuationProjection b).continuous

/-- The lift of a regular-locus path from a prescribed solution germ. -/
noncomputable def zagierContinuationLiftPath (b : zagierODERegularSet)
    (γ : C(I, zagierODERegularSet)) (p : ZagierContinuation b)
    (hγ : γ 0 = zagierContinuationProjection b p) : C(I, ZagierContinuation b) :=
  (isCoveringMap_zagierContinuationProjection b).liftPath γ p hγ

theorem zagierContinuationLiftPath_projects (b : zagierODERegularSet)
    (γ : C(I, zagierODERegularSet)) (p : ZagierContinuation b)
    (hγ : γ 0 = zagierContinuationProjection b p) :
    zagierContinuationProjection b ∘ zagierContinuationLiftPath b γ p hγ = γ :=
  (isCoveringMap_zagierContinuationProjection b).liftPath_lifts γ p hγ

@[simp]
theorem zagierContinuationLiftPath_zero (b : zagierODERegularSet)
    (γ : C(I, zagierODERegularSet)) (p : ZagierContinuation b)
    (hγ : γ 0 = zagierContinuationProjection b p) :
    zagierContinuationLiftPath b γ p hγ 0 = p :=
  (isCoveringMap_zagierContinuationProjection b).liftPath_zero γ p hγ

theorem eq_zagierContinuationLiftPath_iff (b : zagierODERegularSet)
    {γ : C(I, zagierODERegularSet)} {p : ZagierContinuation b}
    (hγ : γ 0 = zagierContinuationProjection b p) {Γ : C(I, ZagierContinuation b)} :
    Γ = zagierContinuationLiftPath b γ p hγ ↔
      zagierContinuationProjection b ∘ Γ = γ ∧ Γ 0 = p :=
  (isCoveringMap_zagierContinuationProjection b).eq_liftPath_iff' hγ

/-- Each initial solution germ has a unique continuous lift along any regular path. -/
theorem existsUnique_zagierContinuation_pathLift (b : zagierODERegularSet)
    (γ : C(I, zagierODERegularSet)) (p : ZagierContinuation b)
    (hγ : γ 0 = zagierContinuationProjection b p) :
    ∃! Γ : C(I, ZagierContinuation b),
      zagierContinuationProjection b ∘ Γ = γ ∧ Γ 0 = p := by
  refine ⟨zagierContinuationLiftPath b γ p hγ,
    ⟨zagierContinuationLiftPath_projects b γ p hγ, zagierContinuationLiftPath_zero b γ p hγ⟩, ?_⟩
  intro Γ hΓ
  exact (eq_zagierContinuationLiftPath_iff b hγ).mpr hΓ

/-- Homotopies fixing the endpoints preserve the endpoint of a lifted solution germ. -/
theorem zagierContinuationLiftPath_end_of_homotopicRel (b : zagierODERegularSet)
    {γ₀ γ₁ : C(I, zagierODERegularSet)} (h : γ₀.HomotopicRel γ₁ {0, 1})
    (p : ZagierContinuation b) (h₀ : γ₀ 0 = zagierContinuationProjection b p)
    (h₁ : γ₁ 0 = zagierContinuationProjection b p) :
    zagierContinuationLiftPath b γ₀ p h₀ 1 = zagierContinuationLiftPath b γ₁ p h₁ 1 :=
  (isCoveringMap_zagierContinuationProjection b).liftPath_apply_one_eq_of_homotopicRel h p h₀ h₁

end DirichletL
