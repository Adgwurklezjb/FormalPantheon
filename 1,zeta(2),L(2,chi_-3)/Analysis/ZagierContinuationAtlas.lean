import Analysis.ZagierSolutionFrames

/-!
The continuation atlas for CDT v2's homogeneous equation `explicitode`.
Its discrete germ fibers and compatible local frames prepare path continuation
for the monodromy argument in Lemma `14functions`.
-/

namespace DirichletL

open Filter Topology Bundle
open scoped Topology Matrix

instance instTopologicalSpaceZagierSolutionGerms (z0 : ℂ) :
    TopologicalSpace (zagierSolutionGerms z0) := ⊥

instance instDiscreteTopologyZagierSolutionGerms (z0 : ℂ) :
    DiscreteTopology (zagierSolutionGerms z0) := ⟨rfl⟩

/-- The total space of actual solution germs over the regular locus. -/
abbrev ZagierContinuation (b : zagierODERegularSet) :=
  Bundle.TotalSpace (zagierSolutionGerms (b : ℂ))
    (fun x : zagierODERegularSet => zagierSolutionGerms (x : ℂ))

/-- The base point of a continuation germ. -/
def zagierContinuationProjection (b : zagierODERegularSet) :
    ZagierContinuation b → zagierODERegularSet := Bundle.TotalSpace.proj

namespace ZagierSolutionFrame

theorem coordinates_change_eq (e e' : ZagierSolutionFrame) (b x y : zagierODERegularSet)
    (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet)
    (hy : y ∈ e.baseSet) (hy' : y ∈ e'.baseSet) (c : zagierSolutionGerms (b : ℂ)) :
    e.coordinates b y (e'.fromCoordinates b y c) =
      e.coordinates b x (e'.fromCoordinates b x c) := by
  apply zagierSolutionGermState_injective b.property
  rw [state_coordinates, state_fromCoordinates, state_coordinates, state_fromCoordinates,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have he := eqOn_zagierFundamentalMatrix_transition
    (Metric.isOpen_ball.inter Metric.isOpen_ball)
    ((convex_ball e.center e.radius).inter (convex_ball e'.center e'.radius)).isPreconnected
    (show (x : ℂ) ∈ Metric.ball e.center e.radius ∩ Metric.ball e'.center e'.radius from ⟨hx, hx'⟩)
    x.property (fun j => (e.analytic j).mono Set.inter_subset_left)
    (fun j => (e.equation j).mono Set.inter_subset_left)
    (fun z hz => e.isUnit_matrix hz.1)
    (fun j => (e'.analytic j).mono Set.inter_subset_right)
    (fun j => (e'.equation j).mono Set.inter_subset_right) ⟨hy, hy'⟩
  dsimp only at he
  rw [he]

/-- Coordinate equivalences are homeomorphisms of discrete solution-germ fibers. -/
noncomputable def coordinatesHomeomorph (e : ZagierSolutionFrame) (b x : zagierODERegularSet)
    (hx : x ∈ e.baseSet) : zagierSolutionGerms (x : ℂ) ≃ₜ zagierSolutionGerms (b : ℂ) where
  toEquiv := (e.coordinatesEquiv b x hx).toEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- A local coordinate chart before assigning a topology to the total space. -/
noncomputable def pretrivialization (e : ZagierSolutionFrame) (b : zagierODERegularSet) :
    Pretrivialization (zagierSolutionGerms (b : ℂ)) (zagierContinuationProjection b) where
  toFun p := (p.proj, e.coordinates b p.proj p.snd)
  invFun q := ⟨q.1, e.fromCoordinates b q.1 q.2⟩
  source := zagierContinuationProjection b ⁻¹' e.baseSet
  target := e.baseSet ×ˢ Set.univ
  map_source' p hp := ⟨hp, Set.mem_univ _⟩
  map_target' q hq := hq.1
  left_inv' p hp := by
    change Bundle.TotalSpace.mk p.proj
      (e.fromCoordinates b p.proj (e.coordinates b p.proj p.snd)) = p
    rw [e.fromCoordinates_coordinates b p.proj hp]
  right_inv' q hq := by
    change (q.1, e.coordinates b q.1 (e.fromCoordinates b q.1 q.2)) = q
    rw [e.coordinates_fromCoordinates b q.1 hq.1]
  open_target := e.isOpen_baseSet.prod isOpen_univ
  baseSet := e.baseSet
  open_baseSet := e.isOpen_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun p hp := rfl

@[simp]
theorem pretrivialization_apply (e : ZagierSolutionFrame) (b : zagierODERegularSet)
    (p : ZagierContinuation b) :
    e.pretrivialization b p = (p.proj, e.coordinates b p.proj p.snd) := rfl

@[simp]
theorem pretrivialization_symm_apply (e : ZagierSolutionFrame) (b : zagierODERegularSet)
    (q : zagierODERegularSet × zagierSolutionGerms (b : ℂ)) :
    (e.pretrivialization b).toPartialEquiv.symm q =
      ⟨q.1, e.fromCoordinates b q.1 q.2⟩ := rfl

theorem continuousOn_change (e e' : ZagierSolutionFrame) (b : zagierODERegularSet) :
    ContinuousOn (e.pretrivialization b ∘ (e'.pretrivialization b).toPartialEquiv.symm)
      ((e'.pretrivialization b).target ∩
        (e'.pretrivialization b).toPartialEquiv.symm ⁻¹' (e.pretrivialization b).source) := by
  change ContinuousOn
    (fun q => (q.1, e.coordinates b q.1 (e'.fromCoordinates b q.1 q.2)))
    {q : zagierODERegularSet × zagierSolutionGerms (b : ℂ) |
      (q.1 ∈ e'.baseSet ∧ q.2 ∈ Set.univ) ∧ q.1 ∈ e.baseSet}
  intro p hp
  have hf : Continuous (fun c : zagierSolutionGerms (b : ℂ) =>
      e.coordinates b p.1 (e'.fromCoordinates b p.1 c)) := continuous_of_discreteTopology
  have hc : Continuous (fun q : zagierODERegularSet × zagierSolutionGerms (b : ℂ) =>
      (q.1, e.coordinates b p.1 (e'.fromCoordinates b p.1 q.2))) :=
    continuous_fst.prodMk (hf.comp continuous_snd)
  apply hc.continuousOn.congr _ p hp
  intro q hq
  exact Prod.ext rfl (e.coordinates_change_eq e' b p.1 q.1 hp.2 hp.1.1 hq.2 hq.1.1 q.2)

end ZagierSolutionFrame

/-- All normalized local solution frames form a compatible continuation atlas. -/
noncomputable def zagierContinuationPrebundle (b : zagierODERegularSet) :
    FiberPrebundle (zagierSolutionGerms (b : ℂ))
      (fun x : zagierODERegularSet => zagierSolutionGerms (x : ℂ)) where
  pretrivializationAtlas := Set.range (fun e : ZagierSolutionFrame => e.pretrivialization b)
  pretrivializationAt x := (ZagierSolutionFrame.atPoint x).pretrivialization b
  mem_base_pretrivializationAt := ZagierSolutionFrame.mem_baseSet_atPoint
  pretrivialization_mem_atlas x := ⟨ZagierSolutionFrame.atPoint x, rfl⟩
  continuous_trivChange := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    exact e.continuousOn_change e' b
  totalSpaceMk_isInducing x := by
    change IsInducing (fun φ => (x, (ZagierSolutionFrame.atPoint x).coordinates b x φ))
    exact Topology.isInducing_const_prod.mpr
      ((ZagierSolutionFrame.atPoint x).coordinatesHomeomorph b x
        (ZagierSolutionFrame.mem_baseSet_atPoint x)).isInducing

end DirichletL
