import Analysis.ZagierContinuation

/-!
Complex-linear transport of homogeneous solution germs along regular paths.
This supplies the monodromy maps used in CDT v2, Lemma `14functions`.
-/

namespace DirichletL

open Filter Topology Bundle unitInterval
open scoped Topology

theorem continuousAt_zagierContinuation_add (b : zagierODERegularSet)
    {T : Type*} [TopologicalSpace T] {x : T → zagierODERegularSet}
    {f g : ∀ t, zagierSolutionGerms (x t : ℂ)} {t : T}
    (hf : ContinuousAt (fun s => (⟨x s, f s⟩ : ZagierContinuation b)) t)
    (hg : ContinuousAt (fun s => (⟨x s, g s⟩ : ZagierContinuation b)) t) :
    ContinuousAt (fun s => (⟨x s, f s + g s⟩ : ZagierContinuation b)) t := by
  let e := ZagierSolutionFrame.atPoint (x t)
  have ht : x t ∈ e.baseSet := ZagierSolutionFrame.mem_baseSet_atPoint _
  have hf' := ((e.trivialization b).tendsto_nhds_iff
    (z := (⟨x t, f t⟩ : ZagierContinuation b))
    ((e.trivialization b).mem_source.mpr ht)).mp hf
  have hg' := ((e.trivialization b).tendsto_nhds_iff
    (z := (⟨x t, g t⟩ : ZagierContinuation b))
    ((e.trivialization b).mem_source.mpr ht)).mp hg
  apply ((e.trivialization b).tendsto_nhds_iff
    (z := (⟨x t, f t + g t⟩ : ZagierContinuation b))
    ((e.trivialization b).mem_source.mpr ht)).mpr
  refine ⟨hf'.1, ?_⟩
  simpa only [ZagierSolutionFrame.trivialization_apply, map_add] using hf'.2.add hg'.2

theorem continuousAt_zagierContinuation_smul (b : zagierODERegularSet)
    {T : Type*} [TopologicalSpace T] {x : T → zagierODERegularSet}
    {f : ∀ t, zagierSolutionGerms (x t : ℂ)} {t : T}
    (hf : ContinuousAt (fun s => (⟨x s, f s⟩ : ZagierContinuation b)) t) (c : ℂ) :
    ContinuousAt (fun s => (⟨x s, c • f s⟩ : ZagierContinuation b)) t := by
  let e := ZagierSolutionFrame.atPoint (x t)
  have ht : x t ∈ e.baseSet := ZagierSolutionFrame.mem_baseSet_atPoint _
  have hf' := ((e.trivialization b).tendsto_nhds_iff
    (z := (⟨x t, f t⟩ : ZagierContinuation b))
    ((e.trivialization b).mem_source.mpr ht)).mp hf
  apply ((e.trivialization b).tendsto_nhds_iff
    (z := (⟨x t, c • f t⟩ : ZagierContinuation b))
    ((e.trivialization b).mem_source.mpr ht)).mpr
  refine ⟨hf'.1, ?_⟩
  have hc : Continuous (fun v : zagierSolutionGerms (b : ℂ) => c • v) :=
    continuous_of_discreteTopology
  simpa only [ZagierSolutionFrame.trivialization_apply, map_smul] using
    (hc.tendsto _).comp hf'.2

/-- Identify solution-germ fibers at equal regular points. -/
noncomputable def zagierSolutionGermsCongr {x y : zagierODERegularSet} (h : x = y) :
    zagierSolutionGerms (x : ℂ) ≃ₗ[ℂ] zagierSolutionGerms (y : ℂ) := by
  subst y
  exact LinearEquiv.refl ℂ _

theorem mk_zagierSolutionGermsCongr (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (h : x = y) (φ : zagierSolutionGerms (x : ℂ)) :
    (⟨y, zagierSolutionGermsCongr h φ⟩ : ZagierContinuation b) = ⟨x, φ⟩ := by
  subst y
  rfl

/-- The covering lift of a path from a specified solution germ. -/
noncomputable def zagierPathLift (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) : C(I, ZagierContinuation b) :=
  zagierContinuationLiftPath b γ.toContinuousMap ⟨x, φ⟩ γ.source

theorem zagierPathLift_proj (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) (t : I) :
    (zagierPathLift b γ φ t).proj = γ t :=
  congrFun (zagierContinuationLiftPath_projects b γ.toContinuousMap ⟨x, φ⟩ γ.source) t

@[simp]
theorem zagierPathLift_zero (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathLift b γ φ 0 = ⟨x, φ⟩ :=
  zagierContinuationLiftPath_zero b γ.toContinuousMap ⟨x, φ⟩ γ.source

/-- The lifted germ viewed in the fiber over the actual path value. -/
noncomputable def zagierPathGerm (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) (t : I) :
    zagierSolutionGerms (γ t : ℂ) :=
  zagierSolutionGermsCongr (zagierPathLift_proj b γ φ t) (zagierPathLift b γ φ t).snd

theorem mk_zagierPathGerm (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) (t : I) :
    (⟨γ t, zagierPathGerm b γ φ t⟩ : ZagierContinuation b) = zagierPathLift b γ φ t :=
  mk_zagierSolutionGermsCongr b (zagierPathLift_proj b γ φ t) _

theorem continuous_zagierPathGerm (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) :
    Continuous (fun t => (⟨γ t, zagierPathGerm b γ φ t⟩ : ZagierContinuation b)) := by
  simpa only [mk_zagierPathGerm] using (zagierPathLift b γ φ).continuous

@[simp]
theorem zagierPathGerm_zero (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathGerm b γ φ 0 = zagierSolutionGermsCongr γ.source.symm φ := by
  apply Bundle.TotalSpace.mk_injective (F := zagierSolutionGerms (b : ℂ))
    (E := fun z : zagierODERegularSet => zagierSolutionGerms (z : ℂ)) (γ 0)
  rw [mk_zagierPathGerm, zagierPathLift_zero, mk_zagierSolutionGermsCongr]

/-- Transport a solution germ to the endpoint of a regular path. -/
noncomputable def zagierPathTransport (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) : zagierSolutionGerms (y : ℂ) :=
  zagierSolutionGermsCongr γ.target (zagierPathGerm b γ φ 1)

theorem zagierPathLift_one (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathLift b γ φ 1 = ⟨y, zagierPathTransport b γ φ⟩ := by
  rw [zagierPathTransport, mk_zagierSolutionGermsCongr, mk_zagierPathGerm]

theorem zagierPathGerm_add (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ ψ : zagierSolutionGerms (x : ℂ)) (t : I) :
    zagierPathGerm b γ (φ + ψ) t = zagierPathGerm b γ φ t + zagierPathGerm b γ ψ t := by
  let Γ : C(I, ZagierContinuation b) :=
    ⟨fun s => ⟨γ s, zagierPathGerm b γ φ s + zagierPathGerm b γ ψ s⟩,
      continuous_iff_continuousAt.mpr (fun s => continuousAt_zagierContinuation_add b
        (continuous_zagierPathGerm b γ φ).continuousAt
        (continuous_zagierPathGerm b γ ψ).continuousAt)⟩
  have hΓ : Γ = zagierPathLift b γ (φ + ψ) := by
    apply (eq_zagierContinuationLiftPath_iff b γ.source).mpr
    refine ⟨rfl, ?_⟩
    change (⟨γ 0, zagierPathGerm b γ φ 0 + zagierPathGerm b γ ψ 0⟩ :
      ZagierContinuation b) = ⟨x, φ + ψ⟩
    rw [zagierPathGerm_zero, zagierPathGerm_zero, ← map_add, mk_zagierSolutionGermsCongr]
  apply Bundle.TotalSpace.mk_injective (F := zagierSolutionGerms (b : ℂ))
    (E := fun z : zagierODERegularSet => zagierSolutionGerms (z : ℂ)) (γ t)
  rw [mk_zagierPathGerm]
  exact (congrArg (fun p : C(I, ZagierContinuation b) => p t) hΓ).symm

theorem zagierPathGerm_smul (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (c : ℂ) (φ : zagierSolutionGerms (x : ℂ)) (t : I) :
    zagierPathGerm b γ (c • φ) t = c • zagierPathGerm b γ φ t := by
  let Γ : C(I, ZagierContinuation b) :=
    ⟨fun s => ⟨γ s, c • zagierPathGerm b γ φ s⟩,
      continuous_iff_continuousAt.mpr (fun s => continuousAt_zagierContinuation_smul b
        (continuous_zagierPathGerm b γ φ).continuousAt c)⟩
  have hΓ : Γ = zagierPathLift b γ (c • φ) := by
    apply (eq_zagierContinuationLiftPath_iff b γ.source).mpr
    refine ⟨rfl, ?_⟩
    change (⟨γ 0, c • zagierPathGerm b γ φ 0⟩ : ZagierContinuation b) = ⟨x, c • φ⟩
    rw [zagierPathGerm_zero, ← map_smul, mk_zagierSolutionGermsCongr]
  apply Bundle.TotalSpace.mk_injective (F := zagierSolutionGerms (b : ℂ))
    (E := fun z : zagierODERegularSet => zagierSolutionGerms (z : ℂ)) (γ t)
  rw [mk_zagierPathGerm]
  exact (congrArg (fun p : C(I, ZagierContinuation b) => p t) hΓ).symm

theorem zagierPathTransport_add (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ ψ : zagierSolutionGerms (x : ℂ)) :
    zagierPathTransport b γ (φ + ψ) = zagierPathTransport b γ φ + zagierPathTransport b γ ψ := by
  simp only [zagierPathTransport, zagierPathGerm_add, map_add]

theorem zagierPathTransport_smul (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (c : ℂ) (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathTransport b γ (c • φ) = c • zagierPathTransport b γ φ := by
  simp only [zagierPathTransport, zagierPathGerm_smul, map_smul]

/-- Endpoint transport is complex-linear. -/
noncomputable def zagierPathTransportLinearMap (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y) :
    zagierSolutionGerms (x : ℂ) →ₗ[ℂ] zagierSolutionGerms (y : ℂ) where
  toFun := zagierPathTransport b γ
  map_add' := zagierPathTransport_add b γ
  map_smul' := zagierPathTransport_smul b γ

@[simp]
theorem zagierPathTransportLinearMap_apply (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathTransportLinearMap b γ φ = zagierPathTransport b γ φ := rfl

/-- The actual lifted path, with its initial and transported endpoints. -/
noncomputable def zagierLiftedPath (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) :
    Path (⟨x, φ⟩ : ZagierContinuation b) ⟨y, zagierPathTransport b γ φ⟩ where
  toContinuousMap := zagierPathLift b γ φ
  source' := zagierPathLift_zero b γ φ
  target' := zagierPathLift_one b γ φ

@[simp]
theorem zagierLiftedPath_apply (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) (t : I) :
    zagierLiftedPath b γ φ t = zagierPathLift b γ φ t := rfl

theorem zagierLiftedPath_projects (b : zagierODERegularSet) {x y : zagierODERegularSet}
    (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) :
    (zagierLiftedPath b γ φ).map (continuous_zagierContinuationProjection b) = γ := by
  apply Path.ext
  funext t
  exact zagierPathLift_proj b γ φ t

theorem zagierPathTransport_eq_of_lift (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y)
    (φ : zagierSolutionGerms (x : ℂ)) (ψ : zagierSolutionGerms (y : ℂ))
    (Γ : Path (⟨x, φ⟩ : ZagierContinuation b) ⟨y, ψ⟩)
    (hΓ : Γ.map (continuous_zagierContinuationProjection b) = γ) :
    zagierPathTransport b γ φ = ψ := by
  have he : Γ.toContinuousMap = zagierPathLift b γ φ := by
    apply (eq_zagierContinuationLiftPath_iff b γ.source).mpr
    refine ⟨?_, Γ.source⟩
    funext t
    exact congrArg (fun p : Path x y => p t) hΓ
  apply Bundle.TotalSpace.mk_injective (F := zagierSolutionGerms (b : ℂ))
    (E := fun z : zagierODERegularSet => zagierSolutionGerms (z : ℂ)) y
  rw [← zagierPathLift_one, ← he]
  exact Γ.target

@[simp]
theorem zagierPathTransport_refl (b x : zagierODERegularSet)
    (φ : zagierSolutionGerms (x : ℂ)) : zagierPathTransport b (Path.refl x) φ = φ := by
  apply zagierPathTransport_eq_of_lift b (Path.refl x) φ φ
    (Path.refl (⟨x, φ⟩ : ZagierContinuation b))
  ext t
  rfl

theorem zagierPathTransport_trans (b : zagierODERegularSet)
    {x y z : zagierODERegularSet} (γ : Path x y) (δ : Path y z)
    (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathTransport b (γ.trans δ) φ =
      zagierPathTransport b δ (zagierPathTransport b γ φ) := by
  apply zagierPathTransport_eq_of_lift b (γ.trans δ) φ _
    ((zagierLiftedPath b γ φ).trans (zagierLiftedPath b δ (zagierPathTransport b γ φ)))
  rw [Path.map_trans, zagierLiftedPath_projects, zagierLiftedPath_projects]

@[simp]
theorem zagierPathTransport_symm (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathTransport b γ.symm (zagierPathTransport b γ φ) = φ := by
  apply zagierPathTransport_eq_of_lift b γ.symm _ φ (zagierLiftedPath b γ φ).symm
  rw [← Path.map_symm, zagierLiftedPath_projects]

/-- Transport along a path is a complex linear equivalence, inverted by reversal. -/
noncomputable def zagierPathTransportEquiv (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y) :
    zagierSolutionGerms (x : ℂ) ≃ₗ[ℂ] zagierSolutionGerms (y : ℂ) :=
  { zagierPathTransportLinearMap b γ with
    invFun := zagierPathTransport b γ.symm
    left_inv := zagierPathTransport_symm b γ
    right_inv := by
      intro ψ
      simpa only [Path.symm_symm] using zagierPathTransport_symm b γ.symm ψ }

@[simp]
theorem zagierPathTransportEquiv_apply (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y) (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathTransportEquiv b γ φ = zagierPathTransport b γ φ := rfl

@[simp]
theorem zagierPathTransportEquiv_symm_apply (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y) (ψ : zagierSolutionGerms (y : ℂ)) :
    (zagierPathTransportEquiv b γ).symm ψ = zagierPathTransport b γ.symm ψ := rfl

theorem zagierPathTransport_of_homotopic (b : zagierODERegularSet)
    {x y : zagierODERegularSet} {γ δ : Path x y} (h : γ.Homotopic δ)
    (φ : zagierSolutionGerms (x : ℂ)) :
    zagierPathTransport b γ φ = zagierPathTransport b δ φ := by
  apply Bundle.TotalSpace.mk_injective (F := zagierSolutionGerms (b : ℂ))
    (E := fun z : zagierODERegularSet => zagierSolutionGerms (z : ℂ)) y
  rw [← zagierPathLift_one, ← zagierPathLift_one]
  exact zagierContinuationLiftPath_end_of_homotopicRel b h ⟨x, φ⟩ γ.source δ.source

theorem zagierPathTransportEquiv_of_homotopic (b : zagierODERegularSet)
    {x y : zagierODERegularSet} {γ δ : Path x y} (h : γ.Homotopic δ) :
    zagierPathTransportEquiv b γ = zagierPathTransportEquiv b δ := by
  apply LinearEquiv.ext
  intro φ
  exact zagierPathTransport_of_homotopic b h φ

end DirichletL
