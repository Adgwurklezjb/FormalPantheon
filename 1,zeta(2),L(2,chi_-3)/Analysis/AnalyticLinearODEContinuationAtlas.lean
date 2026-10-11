import Analysis.AnalyticLinearODEFrames

/-!
The covering atlas of finite analytic matrix solution germs, used for the
regular-locus continuation in CDT v2, Lemma `14functions`.
-/

namespace DirichletL.AnalyticMatrixODE

open Filter Topology Bundle
open scoped Topology

variable {I : Type*} [Fintype I] (D : AnalyticMatrixODE I)

instance instTopologicalSpaceSolutionGerms (z : ℂ) :
    TopologicalSpace (D.solutionGerms z) := ⊥

instance instDiscreteTopologySolutionGerms (z : ℂ) :
    DiscreteTopology (D.solutionGerms z) := ⟨rfl⟩

/-- The total space of actual vector solution germs over the analytic domain. -/
abbrev Continuation (b : D.domain) :=
  Bundle.TotalSpace (D.solutionGerms (b : ℂ))
    (fun x : D.domain => D.solutionGerms (x : ℂ))

/-- The base point of a vector solution germ. -/
def continuationProjection (b : D.domain) : D.Continuation b → D.domain :=
  Bundle.TotalSpace.proj

namespace SolutionFrame

variable {D}

/-- Coordinate equivalences are homeomorphisms of discrete germ fibers. -/
noncomputable def coordinatesHomeomorph (e : D.SolutionFrame) (b x : D.domain)
    (hx : x ∈ e.baseSet) : D.solutionGerms (x : ℂ) ≃ₜ D.solutionGerms (b : ℂ) where
  toEquiv := (e.coordinatesEquiv b x hx).toEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- A frame chart before assigning the total-space topology. -/
noncomputable def pretrivialization (e : D.SolutionFrame) (b : D.domain) :
    Pretrivialization (D.solutionGerms (b : ℂ)) (D.continuationProjection b) where
  toFun p := (p.proj, e.coordinates b p.proj p.snd)
  invFun q := ⟨q.1, e.fromCoordinates b q.1 q.2⟩
  source := D.continuationProjection b ⁻¹' e.baseSet
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
theorem pretrivialization_apply (e : D.SolutionFrame) (b : D.domain)
    (p : D.Continuation b) :
    e.pretrivialization b p = (p.proj, e.coordinates b p.proj p.snd) := rfl

@[simp]
theorem pretrivialization_symm_apply (e : D.SolutionFrame) (b : D.domain)
    (q : D.domain × D.solutionGerms (b : ℂ)) :
    (e.pretrivialization b).toPartialEquiv.symm q =
      ⟨q.1, e.fromCoordinates b q.1 q.2⟩ := rfl

theorem continuousOn_change (e e' : D.SolutionFrame) (b : D.domain) :
    ContinuousOn (e.pretrivialization b ∘ (e'.pretrivialization b).toPartialEquiv.symm)
      ((e'.pretrivialization b).target ∩
        (e'.pretrivialization b).toPartialEquiv.symm ⁻¹' (e.pretrivialization b).source) := by
  change ContinuousOn
    (fun q => (q.1, e.coordinates b q.1 (e'.fromCoordinates b q.1 q.2)))
    {q : D.domain × D.solutionGerms (b : ℂ) |
      (q.1 ∈ e'.baseSet ∧ q.2 ∈ Set.univ) ∧ q.1 ∈ e.baseSet}
  intro p hp
  have hf : Continuous (fun c : D.solutionGerms (b : ℂ) =>
      e.coordinates b p.1 (e'.fromCoordinates b p.1 c)) := continuous_of_discreteTopology
  have hc : Continuous (fun q : D.domain × D.solutionGerms (b : ℂ) =>
      (q.1, e.coordinates b p.1 (e'.fromCoordinates b p.1 q.2))) :=
    continuous_fst.prodMk (hf.comp continuous_snd)
  apply hc.continuousOn.congr _ p hp
  intro q hq
  exact Prod.ext rfl (e.coordinates_change_eq e' b p.1 q.1 hp.2 hp.1.1 hq.2 hq.1.1 q.2)

end SolutionFrame

/-- All normalized vector solution frames form a compatible atlas. -/
noncomputable def continuationPrebundle (b : D.domain) :
    FiberPrebundle (D.solutionGerms (b : ℂ))
      (fun x : D.domain => D.solutionGerms (x : ℂ)) where
  pretrivializationAtlas := Set.range (fun e : D.SolutionFrame => e.pretrivialization b)
  pretrivializationAt x := (SolutionFrame.atPoint x).pretrivialization b
  mem_base_pretrivializationAt := SolutionFrame.mem_baseSet_atPoint
  pretrivialization_mem_atlas x := ⟨SolutionFrame.atPoint x, rfl⟩
  continuous_trivChange := by
    rintro _ ⟨e, rfl⟩ _ ⟨e', rfl⟩
    exact e.continuousOn_change e' b
  totalSpaceMk_isInducing x := by
    change IsInducing (fun φ => (x, (SolutionFrame.atPoint x).coordinates b x φ))
    exact Topology.isInducing_const_prod.mpr
      ((SolutionFrame.atPoint x).coordinatesHomeomorph b x
        (SolutionFrame.mem_baseSet_atPoint x)).isInducing

end DirichletL.AnalyticMatrixODE
