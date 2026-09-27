import Analysis.ZagierPullbackDecomposition

/-!
Canonical complementary solution subspaces for CDT v2, `14functions`.
They are defined in the actual fourth-order germ fiber using the coordinate `y in x`.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- Fourth-order germs whose coordinate pullback solves the source equation. -/
noncomputable def zagierSourceSummand {x : ℂ} (hx : x ≠ 1) :
    Submodule ℂ (zagierSolutionGerms (mobiusCoordinate x)) where
  carrier := {φ | ∃ f : ℂ → ℂ, AnalyticAt ℂ f x ∧
    zagierSecondOrderODE f =ᶠ[𝓝 x] 0 ∧
      mobiusGermPullback hx (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f}
  zero_mem' := ⟨0, analyticAt_const,
    Filter.Eventually.of_forall (fun z => by simp [zagierSecondOrderODE]), by simp⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf, hfo, hφ⟩ ⟨g, hg, hgo, hψ⟩
    refine ⟨f + g, hf.add hg, ?_, ?_⟩
    · filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, hfo, hgo]
        with z hfz hgz hfe hge
      simpa [hfe, hge] using zagierSecondOrderODE_linearCombination hfz hgz 1 1
    · simp only [Submodule.coe_add, map_add, hφ, hψ]
      rfl
  smul_mem' := by
    rintro c φ ⟨f, hf, hfo, hφ⟩
    refine ⟨c • f, hf.const_smul (c := c), ?_, ?_⟩
    · filter_upwards [hf.eventually_analyticAt, hfo] with z hfz hfe
      simpa [smul_eq_mul, hfe] using
        zagierSecondOrderODE_linearCombination (g := 0) hfz analyticAt_const c 0
    · simp only [Submodule.coe_smul, map_smul, hφ]
      rfl

/-- Fourth-order germs whose coordinate pullback solves the conjugate equation. -/
noncomputable def zagierConjugateSummand {x : ℂ} (hx : x ≠ 1) :
    Submodule ℂ (zagierSolutionGerms (mobiusCoordinate x)) where
  carrier := {φ | ∃ f : ℂ → ℂ, AnalyticAt ℂ f x ∧
    zagierConjugateAnalyticODE f =ᶠ[𝓝 x] 0 ∧
      mobiusGermPullback hx (φ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = f}
  zero_mem' := ⟨0, analyticAt_const,
    Filter.Eventually.of_forall (fun z => by simp [zagierConjugateAnalyticODE]), by simp⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf, hfo, hφ⟩ ⟨g, hg, hgo, hψ⟩
    refine ⟨f + g, hf.add hg, ?_, ?_⟩
    · filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, hfo, hgo]
        with z hfz hgz hfe hge
      simpa [hfe, hge] using zagierConjugateAnalyticODE_linearCombination hfz hgz 1 1
    · simp only [Submodule.coe_add, map_add, hφ, hψ]
      rfl
  smul_mem' := by
    rintro c φ ⟨f, hf, hfo, hφ⟩
    refine ⟨c • f, hf.const_smul (c := c), ?_, ?_⟩
    · filter_upwards [hf.eventually_analyticAt, hfo] with z hfz hfe
      simpa [smul_eq_mul, hfe] using
        zagierConjugateAnalyticODE_linearCombination (g := 0) hfz analyticAt_const c 0
    · simp only [Submodule.coe_smul, map_smul, hφ]
      rfl

theorem isCompl_zagierSolutionSummands {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet) :
    IsCompl (zagierSourceSummand hx) (zagierConjugateSummand hx) := by
  obtain ⟨hx₀, hx₂⟩ := mobiusCoordinate_regular_ne_zero_two hreg
  refine ⟨Submodule.disjoint_def.mpr ?_, codisjoint_iff_le_sup.mpr ?_⟩
  · rintro φ ⟨f, hf, hE, hφ⟩ ⟨g, _, hC, hψ⟩
    have he := Germ.coe_eq.mp (hφ.symm.trans hψ)
    have hzero := eventuallyEq_zero_of_zagierSecondOrder_and_conjugate hx hreg hf hE
      ((eventuallyEq_zagierConjugateAnalyticODE he).trans hC)
    apply Subtype.ext
    apply mobiusGermPullback_injective hx₀ hx hx₂
    simpa only [hφ, Submodule.coe_zero, map_zero] using Germ.coe_eq.mpr hzero
  · intro φ _
    obtain ⟨f, g, hf, hg, hE, hC, hsum⟩ := exists_zagierPullback_decomposition hx hreg φ
    obtain ⟨ψ, hψ⟩ := exists_zagierSolutionGerm_mobiusPullback hx₀ hx hx₂ hf hE
    obtain ⟨u, hu, huo, hue⟩ := exists_zagierAnalyticODE_of_pullback hx₀ hx hx₂ hg
      (eventually_zagierPullbackAnalyticODE_of_conjugate hx hg hC)
    let θ := zagierSolutionGermOfFun u hu huo
    have hθ : mobiusGermPullback hx (θ : Germ (𝓝 (mobiusCoordinate x)) ℂ) = g :=
      Germ.coe_eq.mpr hue
    apply Submodule.mem_sup.mpr
    refine ⟨ψ, ⟨f, hf, hE, hψ⟩, θ, ⟨g, hg, hC, hθ⟩, ?_⟩
    apply Subtype.ext
    apply mobiusGermPullback_injective hx₀ hx hx₂
    simp only [Submodule.coe_add, map_add, hψ, hθ, hsum]
    rfl

end DirichletL
