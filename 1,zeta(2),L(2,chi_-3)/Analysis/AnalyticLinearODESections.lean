import Analysis.AnalyticLinearODEContinuation

/-!
Actual global representatives of the existing regular solution-germ covering.
Source: CDT v2 TeX 1739-1744 and 7157-7173. The full prior meanings and
-/

namespace DirichletL.AnalyticMatrixODE

open Filter Bundle
open scoped Topology Matrix

variable {I : Type*} [Fintype I] (D : AnalyticMatrixODE I)

theorem exists_analytic_representative_of_continuation_section (b : D.domain)
    {u : D.domain → D.Continuation b} (hu : Continuous u)
    (hp : ∀ z, (u z).proj = z) :
    ∃ f : ℂ → I → ℂ, AnalyticOnNhd ℂ f D.domain ∧
      (∀ z ∈ D.domain, HasDerivAt f (D.matrix z *ᵥ f z) z) ∧
      ∀ z : D.domain,
        ((u z).snd : Germ (𝓝 ((u z).proj : ℂ)) (I → ℂ)) = f := by
  classical
  let f (z : ℂ) : I → ℂ := if hz : z ∈ D.domain then
    D.germValue ((u ⟨z, hz⟩).proj : ℂ) (u ⟨z, hz⟩).snd else 0
  have hrep (z : D.domain) :
      ((u z).snd : Germ (𝓝 ((u z).proj : ℂ)) (I → ℂ)) = f := by
    obtain ⟨e, _, g, _, _, hnear⟩ :=
      D.exists_continuation_local_representative b (hu.continuousAt (x := z))
    have he : ∀ᶠ w : D.domain in 𝓝 z, f (w : ℂ) = g (w : ℂ) := by
      filter_upwards [hnear] with w hw
      dsimp only [f]
      rw [dif_pos w.property]
      change Germ.value ((u w).snd : Germ (𝓝 ((u w).proj : ℂ)) (I → ℂ)) = g (w : ℂ)
      rw [hw.2]
      change g ((u w).proj : ℂ) = g (w : ℂ)
      rw [hp w]
    have he' : f =ᶠ[𝓝 (z : ℂ)] g := by
      change ∀ᶠ w in Filter.map ((↑) : D.domain → ℂ) (𝓝 z), f w = g w at he
      rw [map_nhds_subtype_coe_eq_nhds z.property
        (D.isOpen_domain.mem_nhds z.property)] at he
      exact he
    apply hnear.self_of_nhds.2.trans
    apply Germ.coe_eq.mpr
    simpa only [hp z] using he'.symm
  have hf (z : D.domain) : AnalyticAt ℂ f (z : ℂ) ∧
      ∀ᶠ w in 𝓝 (z : ℂ), HasDerivAt f (D.matrix w *ᵥ f w) w := by
    have hg : (f : Germ (𝓝 ((u z).proj : ℂ)) (I → ℂ)) ∈
        D.solutionGerms ((u z).proj : ℂ) := by
      rw [← hrep z]
      exact (u z).snd.property
    simpa only [hp z] using D.mem_solutionGerms_iff.mp hg
  exact ⟨f, fun z hz => (hf ⟨z, hz⟩).1,
    fun z hz => (hf ⟨z, hz⟩).2.self_of_nhds, hrep⟩

theorem exists_analytic_solution_of_simplyConnected
    [SimplyConnectedSpace D.domain] [LocPathConnectedSpace D.domain]
    (b : D.domain) (f : ℂ → I → ℂ) (hf : AnalyticAt ℂ f (b : ℂ))
    (hfo : ∀ᶠ z in 𝓝 (b : ℂ), HasDerivAt f (D.matrix z *ᵥ f z) z) :
    ∃ g : ℂ → I → ℂ, AnalyticOnNhd ℂ g D.domain ∧
      (∀ z ∈ D.domain, HasDerivAt g (D.matrix z *ᵥ g z) z) ∧
      g =ᶠ[𝓝 (b : ℂ)] f := by
  let p : D.Continuation b := ⟨b, D.solutionGermOfFun f hf hfo⟩
  obtain ⟨u, hu, _⟩ := (D.isCoveringMap_continuationProjection b).existsUnique_continuousMap_lifts
    (ContinuousMap.id D.domain) b p rfl
  have hp (z : D.domain) : (u z).proj = z := congrFun hu.2 z
  obtain ⟨g, hga, hgo, hgrep⟩ :=
    D.exists_analytic_representative_of_continuation_section b u.continuous hp
  refine ⟨g, hga, hgo, ?_⟩
  have h := hgrep b
  rw [hu.1] at h
  exact (Germ.coe_eq.mp h).symm

end DirichletL.AnalyticMatrixODE
