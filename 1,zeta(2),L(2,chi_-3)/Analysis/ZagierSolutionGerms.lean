import Analysis.ZagierFundamentalMatrix

/-!
Canonical homogeneous solution germs for CDT v2 equation `explicitode`.
Their regular initial-state coordinates supply the fibers of the continuation
space needed in the proof of Lemma `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

theorem zagierODEState_add {f g : ℂ → ℂ} {z0 : ℂ}
    (hf : AnalyticAt ℂ f z0) (hg : AnalyticAt ℂ g z0) :
    zagierODEState (f + g) z0 = zagierODEState f z0 + zagierODEState g z0 := by
  have h : ∀ j : Fin 2, AnalyticAt ℂ (![f, g] j) z0 := by
    intro j
    fin_cases j
    · exact hf
    · exact hg
  simpa [Fin.sum_univ_two] using zagierODEState_sum h (fun _ => 1)

theorem zagierODEState_smul {f : ℂ → ℂ} {z0 : ℂ}
    (hf : AnalyticAt ℂ f z0) (c : ℂ) :
    zagierODEState (c • f) z0 = c • zagierODEState f z0 := by
  simpa using zagierODEState_sum (J := Unit) (fun _ => hf) (fun _ => c)

theorem zagierAnalyticODE_add {f g : ℂ → ℂ} {z0 : ℂ}
    (hf : AnalyticAt ℂ f z0) (hg : AnalyticAt ℂ g z0) :
    zagierAnalyticODE (f + g) z0 = zagierAnalyticODE f z0 + zagierAnalyticODE g z0 := by
  have h : ∀ j : Fin 2, AnalyticAt ℂ (![f, g] j) z0 := by
    intro j
    fin_cases j
    · exact hf
    · exact hg
  simpa [Fin.sum_univ_two] using zagierAnalyticODE_sum h (fun _ => 1)

theorem zagierAnalyticODE_smul {f : ℂ → ℂ} {z0 : ℂ}
    (hf : AnalyticAt ℂ f z0) (c : ℂ) :
    zagierAnalyticODE (c • f) z0 = c • zagierAnalyticODE f z0 := by
  simpa using zagierAnalyticODE_sum (J := Unit) (fun _ => hf) (fun _ => c)

/-- The complex submodule of analytic germs satisfying the homogeneous equation. -/
noncomputable def zagierSolutionGerms (z0 : ℂ) : Submodule ℂ (Germ (𝓝 z0) ℂ) where
  carrier := {φ | ∃ f : ℂ → ℂ, AnalyticAt ℂ f z0 ∧
    zagierAnalyticODE f =ᶠ[𝓝 z0] 0 ∧ (f : Germ (𝓝 z0) ℂ) = φ}
  zero_mem' := ⟨0, analyticAt_const,
    Filter.Eventually.of_forall (fun z => by simp [zagierAnalyticODE]), rfl⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf, hfo, rfl⟩ ⟨g, hg, hgo, rfl⟩
    refine ⟨f + g, hf.add hg, ?_, rfl⟩
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, hfo, hgo]
      with z hfz hgz hfe hge
    simp only [zagierAnalyticODE_add hfz hgz, hfe, hge, Pi.zero_apply, add_zero]
  smul_mem' := by
    rintro c φ ⟨f, hf, hfo, rfl⟩
    refine ⟨c • f, hf.const_smul (c := c), ?_, rfl⟩
    filter_upwards [hf.eventually_analyticAt, hfo] with z hfz hfe
    simp only [zagierAnalyticODE_smul hfz, hfe, Pi.zero_apply, smul_zero]

theorem mem_zagierSolutionGerms_iff {f : ℂ → ℂ} {z0 : ℂ} :
    (f : Germ (𝓝 z0) ℂ) ∈ zagierSolutionGerms z0 ↔
      AnalyticAt ℂ f z0 ∧ zagierAnalyticODE f =ᶠ[𝓝 z0] 0 := by
  constructor
  · rintro ⟨g, hg, hgo, hgf⟩
    have he := Germ.coe_eq.mp hgf
    exact ⟨hg.congr he, (eventuallyEq_zagierAnalyticODE he.symm).trans hgo⟩
  · rintro ⟨hf, hfo⟩
    exact ⟨f, hf, hfo, rfl⟩

/-- Package an analytic solution as its canonical germ. -/
noncomputable def zagierSolutionGermOfFun {z0 : ℂ} (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f z0) (hfo : zagierAnalyticODE f =ᶠ[𝓝 z0] 0) :
    zagierSolutionGerms z0 :=
  ⟨f, mem_zagierSolutionGerms_iff.mpr ⟨hf, hfo⟩⟩

@[simp]
theorem zagierSolutionGermOfFun_coe {z0 : ℂ} (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f z0) (hfo : zagierAnalyticODE f =ᶠ[𝓝 z0] 0) :
    (zagierSolutionGermOfFun f hf hfo : Germ (𝓝 z0) ℂ) = f := rfl

/-- Initial derivative states descend to the canonical germ quotient by locality. -/
noncomputable def zagierGermState (z0 : ℂ) (φ : Germ (𝓝 z0) ℂ) : Fin 4 → ℂ :=
  φ.liftOn (fun f => zagierODEState f z0)
    (fun _ _ h => (eventuallyEq_zagierODEState h).self_of_nhds)

@[simp]
theorem zagierGermState_coe (z0 : ℂ) (f : ℂ → ℂ) :
    zagierGermState z0 f = zagierODEState f z0 := rfl

/-- The initial-state map is complex-linear on analytic solution germs. -/
noncomputable def zagierSolutionGermState (z0 : ℂ) :
    zagierSolutionGerms z0 →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun φ := zagierGermState z0 φ
  map_add' φ ψ := by
    obtain ⟨f, hf, _, hφ⟩ := φ.property
    obtain ⟨g, hg, _, hψ⟩ := ψ.property
    change zagierGermState z0 (φ.val + ψ.val) =
      zagierGermState z0 φ.val + zagierGermState z0 ψ.val
    rw [← hφ, ← hψ, ← Germ.coe_add]
    exact zagierODEState_add hf hg
  map_smul' c φ := by
    obtain ⟨f, hf, _, hφ⟩ := φ.property
    change zagierGermState z0 (c • φ.val) = c • zagierGermState z0 φ.val
    rw [← hφ, ← Germ.coe_smul]
    exact zagierODEState_smul hf c

@[simp]
theorem zagierSolutionGermState_ofFun {z0 : ℂ} (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f z0) (hfo : zagierAnalyticODE f =ᶠ[𝓝 z0] 0) :
    zagierSolutionGermState z0 (zagierSolutionGermOfFun f hf hfo) =
      zagierODEState f z0 := rfl

theorem zagierSolutionGermState_injective {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet) :
    Function.Injective (zagierSolutionGermState z0) := by
  intro φ ψ he
  obtain ⟨f, hf, hfo, hφ⟩ := φ.property
  obtain ⟨g, hg, hgo, hψ⟩ := ψ.property
  change zagierGermState z0 φ.val = zagierGermState z0 ψ.val at he
  rw [← hφ, ← hψ] at he
  apply Subtype.ext
  rw [← hφ, ← hψ]
  exact Germ.coe_eq.mpr (eventuallyEq_of_zagierAnalyticODE hf hg hreg he hfo hgo)

theorem zagierSolutionGermState_surjective {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet) :
    Function.Surjective (zagierSolutionGermState z0) := by
  intro v
  obtain ⟨f, hf, hinit, hfo⟩ := exists_analytic_zagierODE hreg v
  exact ⟨zagierSolutionGermOfFun f hf hfo, hinit⟩

/-- Regular solution germs are identified with their four initial derivative values. -/
noncomputable def zagierSolutionGermStateEquiv {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet) :
    zagierSolutionGerms z0 ≃ₗ[ℂ] (Fin 4 → ℂ) :=
  LinearEquiv.ofBijective (zagierSolutionGermState z0)
    ⟨zagierSolutionGermState_injective hreg, zagierSolutionGermState_surjective hreg⟩

@[simp]
theorem zagierSolutionGermStateEquiv_apply {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet)
    (φ : zagierSolutionGerms z0) :
    zagierSolutionGermStateEquiv hreg φ = zagierSolutionGermState z0 φ := rfl

@[simp]
theorem zagierSolutionGermStateEquiv_apply_symm {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet)
    (v : Fin 4 → ℂ) :
    zagierSolutionGermState z0 ((zagierSolutionGermStateEquiv hreg).symm v) = v :=
  (zagierSolutionGermStateEquiv hreg).apply_symm_apply v

@[simp]
theorem zagierSolutionGermStateEquiv_symm_apply {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet)
    (φ : zagierSolutionGerms z0) :
    (zagierSolutionGermStateEquiv hreg).symm (zagierSolutionGermState z0 φ) = φ :=
  (zagierSolutionGermStateEquiv hreg).symm_apply_apply φ

theorem finiteDimensional_zagierSolutionGerms {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet) :
    FiniteDimensional ℂ (zagierSolutionGerms z0) :=
  (zagierSolutionGermStateEquiv hreg).symm.finiteDimensional

theorem finrank_zagierSolutionGerms {z0 : ℂ} (hreg : z0 ∈ zagierODERegularSet) :
    Module.finrank ℂ (zagierSolutionGerms z0) = 4 := by
  simpa using (zagierSolutionGermStateEquiv hreg).finrank_eq

end DirichletL
