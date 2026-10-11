import Analysis.AnalyticLinearODEExistence
import Analysis.AnalyticLinearODE

/-!
Finite analytic matrix systems and their solution germs, for the continuation
step of CDT v2 Lemma `14functions`. Evaluation is an isomorphism at each regular
point by the kernel-checked analytic existence and uniqueness theorems.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

variable (I : Type*) [Fintype I]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- A finite complex matrix system with analytic coefficients on an open domain. -/
structure AnalyticMatrixODE where
  /-- The open set on which the coefficient matrix is analytic. -/
  domain : Set ℂ
  isOpen_domain : IsOpen domain
  /-- The matrix multiplying the solution vector in its first derivative. -/
  matrix : ℂ → Matrix I I ℂ
  analytic : AnalyticOnNhd ℂ matrix domain

namespace AnalyticMatrixODE

variable {I} (D : AnalyticMatrixODE I)

/-- Full vector germs represented by analytic solutions of the matrix system. -/
noncomputable def solutionGerms (z : ℂ) : Submodule ℂ (Germ (𝓝 z) (I → ℂ)) where
  carrier := {φ | ∃ f : ℂ → I → ℂ, AnalyticAt ℂ f z ∧
    (∀ᶠ w in 𝓝 z, HasDerivAt f (D.matrix w *ᵥ f w) w) ∧
      (f : Germ (𝓝 z) (I → ℂ)) = φ}
  zero_mem' := ⟨0, analyticAt_const,
    Filter.Eventually.of_forall (fun w => by simpa using hasDerivAt_const w (0 : I → ℂ)),
    rfl⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf, hfo, rfl⟩ ⟨g, hg, hgo, rfl⟩
    refine ⟨f + g, hf.add hg, ?_, rfl⟩
    filter_upwards [hfo, hgo] with w hfw hgw
    simpa only [Pi.add_apply, Matrix.mulVec_add] using hfw.add hgw
  smul_mem' := by
    rintro c φ ⟨f, hf, hfo, rfl⟩
    refine ⟨c • f, hf.const_smul (c := c), ?_, rfl⟩
    filter_upwards [hfo] with w hfw
    simpa only [Pi.smul_apply, Matrix.mulVec_smul] using hfw.const_smul c

theorem mem_solutionGerms_iff {f : ℂ → I → ℂ} {z : ℂ} :
    (f : Germ (𝓝 z) (I → ℂ)) ∈ D.solutionGerms z ↔
      AnalyticAt ℂ f z ∧ (∀ᶠ w in 𝓝 z, HasDerivAt f (D.matrix w *ᵥ f w) w) := by
  constructor
  · rintro ⟨g, hg, hgo, hgf⟩
    have he := Germ.coe_eq.mp hgf
    refine ⟨hg.congr he, ?_⟩
    filter_upwards [hgo, he.eventually_nhds] with w hgw hew
    change g =ᶠ[𝓝 w] f at hew
    simpa only [hew.self_of_nhds] using hgw.congr_of_eventuallyEq hew.symm
  · rintro ⟨hf, hfo⟩
    exact ⟨f, hf, hfo, rfl⟩

/-- Package a specified local analytic vector solution as a solution germ. -/
noncomputable def solutionGermOfFun {z : ℂ} (f : ℂ → I → ℂ)
    (hf : AnalyticAt ℂ f z)
    (hfo : ∀ᶠ w in 𝓝 z, HasDerivAt f (D.matrix w *ᵥ f w) w) :
    D.solutionGerms z :=
  ⟨f, D.mem_solutionGerms_iff.mpr ⟨hf, hfo⟩⟩

@[simp]
theorem solutionGermOfFun_coe {z : ℂ} (f : ℂ → I → ℂ)
    (hf : AnalyticAt ℂ f z)
    (hfo : ∀ᶠ w in 𝓝 z, HasDerivAt f (D.matrix w *ᵥ f w) w) :
    (D.solutionGermOfFun f hf hfo : Germ (𝓝 z) (I → ℂ)) = f := rfl

/-- The canonical germ evaluation map restricted to analytic solution germs. -/
noncomputable def germValue (z : ℂ) : D.solutionGerms z →ₗ[ℂ] (I → ℂ) :=
  (Germ.valueₗ (𝕜 := ℂ) (x := z)).comp (D.solutionGerms z).subtype

@[simp]
theorem germValue_ofFun {z : ℂ} (f : ℂ → I → ℂ)
    (hf : AnalyticAt ℂ f z)
    (hfo : ∀ᶠ w in 𝓝 z, HasDerivAt f (D.matrix w *ᵥ f w) w) :
    D.germValue z (D.solutionGermOfFun f hf hfo) = f z := rfl

theorem germValue_injective {z : ℂ} (hz : z ∈ D.domain) :
    Function.Injective (D.germValue z) := by
  intro φ ψ he
  obtain ⟨f, hf, hfo, hφ⟩ := φ.property
  obtain ⟨g, hg, hgo, hψ⟩ := ψ.property
  change Germ.value φ.val = Germ.value ψ.val at he
  rw [← hφ, ← hψ] at he
  apply Subtype.ext
  rw [← hφ, ← hψ]
  exact Germ.coe_eq.mpr (eventuallyEq_of_analytic_matrix_ode
    (D.analytic z hz).continuousAt hf hg he hfo hgo)

theorem germValue_surjective {z : ℂ} (hz : z ∈ D.domain) :
    Function.Surjective (D.germValue z) := by
  intro v
  obtain ⟨f, hf, hinit, hfo⟩ := exists_analytic_matrix_ode (D.analytic z hz) v
  exact ⟨D.solutionGermOfFun f hf hfo, hinit⟩

/-- Initial values are linear coordinates on the solution-germ space. -/
noncomputable def germValueEquiv {z : ℂ} (hz : z ∈ D.domain) :
    D.solutionGerms z ≃ₗ[ℂ] (I → ℂ) :=
  LinearEquiv.ofBijective (D.germValue z)
    ⟨D.germValue_injective hz, D.germValue_surjective hz⟩

@[simp]
theorem germValueEquiv_apply {z : ℂ} (hz : z ∈ D.domain) (φ : D.solutionGerms z) :
    D.germValueEquiv hz φ = D.germValue z φ := rfl

@[simp]
theorem germValueEquiv_apply_symm {z : ℂ} (hz : z ∈ D.domain) (v : I → ℂ) :
    D.germValue z ((D.germValueEquiv hz).symm v) = v :=
  (D.germValueEquiv hz).apply_symm_apply v

end AnalyticMatrixODE

end DirichletL
