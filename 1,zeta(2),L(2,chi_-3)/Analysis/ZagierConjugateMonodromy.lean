import Analysis.ZagierConjugateLoops
import Analysis.ZagierEndpointMonodromy

/-!
Endpoint shears with their action on the conjugate summand, for CDT v2, `14functions`.
The source formulas and conjugate action use the same actual projected loops.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

theorem exists_zagierEndpoint_endpointCircle_transport_shear_fixedConjugate
    (b : zagierODERegularSet) :
    ∃ q : ℝ, ∃ hq : q ∈ Ioo 0 (1 / 9 : ℝ),
      ∃ γ : Path (⟨mobiusCoordinate q, mobiusCoordinate_regular_of_mem_Ioo hq⟩ : zagierODERegularSet)
        ⟨mobiusCoordinate q, mobiusCoordinate_regular_of_mem_Ioo hq⟩,
      ∃ k : ℂ, k ≠ 0 ∧
        (∀ φ ψ : zagierSolutionGerms (mobiusCoordinate q),
          mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
            (φ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierAnalytic →
          mobiusGermPullback (zagierEndpointInterval_noncritical hq).2.1
            (ψ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = zagierEndpointSolution →
          zagierPathTransport b γ φ = φ + k • ψ ∧ zagierPathTransport b γ ψ = ψ) ∧
        ∀ χ : zagierSolutionGerms (mobiusCoordinate q),
          χ ∈ zagierConjugateSummand (zagierEndpointInterval_noncritical hq).2.1 →
            zagierPathTransport b γ χ = χ := by
  obtain ⟨R, hR, hfixed⟩ := exists_zagierConjugate_trivial_transport_ball
    (z0 := (1 / 9 : ℂ)) (by norm_num)
  obtain ⟨S, hS, hsmall⟩ := exists_zagierEndpointCircle_radius_subset_ball hR
  obtain ⟨q, hq, r, hr, hrS, hqr, γ, hproj, k, hk, hshear⟩ :=
    exists_zagierEndpoint_endpointCircle_transport_shear_lt b hS
  have he : (q : ℂ) = zagierEndpointCoordinate (r : ℂ) :=
    (congrArg (fun s : ℝ => (s : ℂ)) hqr).trans (zagierEndpointCoordinate_ofReal r).symm
  let δ : Path (q : ℂ) (q : ℂ) := (zagierEndpointCirclePath r hr).cast he he
  have hδ (t : I) : δ t ∈ Metric.ball (1 / 9 : ℂ) R := hsmall r hr hrS t
  have h₁ (t : I) : δ t ≠ 1 := by
    change zagierEndpointCoordinate (complexCirclePath r t) ≠ 1
    exact zagierEndpointCoordinate_ne_one
      (complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t)
  have hreg (t : I) : mobiusCoordinate (δ t) ∈ zagierODERegularSet := by
    rw [show mobiusCoordinate (δ t) = (γ t : ℂ) from (hproj t).symm]
    exact (γ t).property
  have hγ : γ = zagierMobiusPath δ h₁ hreg := by
    apply Path.ext
    funext t
    exact Subtype.ext (hproj t)
  refine ⟨q, hq, γ, k, hk, hshear, ?_⟩
  intro χ hχ
  rw [hγ]
  exact hfixed b δ hδ h₁ hreg (zagierEndpointInterval_noncritical hq).2.1 χ hχ

theorem zagierPathTransport_zagierEndpointPath_mem_conjugate_iff
    (b : zagierODERegularSet) {r s : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (hs : s ∈ Ioo 0 (1 / 9 : ℝ))
    (φ : zagierSolutionGerms (mobiusCoordinate r)) :
    zagierPathTransport b (zagierEndpointPath hr hs) φ ∈
      zagierConjugateSummand (zagierEndpointInterval_noncritical hs).2.1 ↔
        φ ∈ zagierConjugateSummand (zagierEndpointInterval_noncritical hr).2.1 := by
  exact zagierPathTransport_mem_conjugateSummand_iff b
    ((zagierEndpointRealPath hr hs).map Complex.continuous_ofReal)
    (fun t => (zagierEndpointInterval_noncritical (zagierEndpointRealPath_mem hr hs t)).2.1)
    (fun t => mobiusCoordinate_regular_of_mem_Ioo (zagierEndpointRealPath_mem hr hs t))
    (zagierEndpointInterval_noncritical hr).2.1 (zagierEndpointInterval_noncritical hs).2.1 φ

theorem exists_zagierEndpoint_commonBase_transport_shears_fixedConjugate {r : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) (φ ψ : zagierSolutionGerms (mobiusCoordinate r))
    (hφ : mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
      (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierAnalytic)
    (hψ : mobiusGermPullback (zagierEndpointInterval_noncritical hr).2.1
      (ψ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = zagierEndpointSolution) :
    let b : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
    ∃ γ δ : Path b b, ∃ k l : ℂ, k ≠ 0 ∧ l ≠ 0 ∧
      zagierPathTransport b γ φ = φ ∧ zagierPathTransport b γ ψ = ψ + k • φ ∧
      zagierPathTransport b δ φ = φ + l • ψ ∧ zagierPathTransport b δ ψ = ψ ∧
      (∀ χ : zagierSolutionGerms (mobiusCoordinate r),
        χ ∈ zagierConjugateSummand (zagierEndpointInterval_noncritical hr).2.1 →
          zagierPathTransport b γ χ ∈
            zagierConjugateSummand (zagierEndpointInterval_noncritical hr).2.1) ∧
      ∀ χ : zagierSolutionGerms (mobiusCoordinate r),
        χ ∈ zagierConjugateSummand (zagierEndpointInterval_noncritical hr).2.1 →
          zagierPathTransport b δ χ = χ := by
  let b : zagierODERegularSet := ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
  obtain ⟨s, hs, γ, hproj, k, hk, hγ⟩ := exists_zagierEndpoint_circle_transport_shear b
  obtain ⟨t, ht, δ, l, hl, hδ, hδC⟩ :=
    exists_zagierEndpoint_endpointCircle_transport_shear_fixedConjugate b
  have hγ₁ (u : I) : complexCirclePath s u ≠ 1 :=
    complexCirclePath_ne_one (by rw [abs_of_pos hs.1]; linarith [hs.2]) u
  have hγreg (u : I) : mobiusCoordinate (complexCirclePath s u) ∈ zagierODERegularSet := by
    rw [← hproj u]
    exact (γ u).property
  have hγeq : γ = zagierMobiusPath (complexCirclePath s) hγ₁ hγreg := by
    apply Path.ext
    funext u
    exact Subtype.ext (hproj u)
  have hγC (χ : zagierSolutionGerms (mobiusCoordinate s))
      (hχ : χ ∈ zagierConjugateSummand (zagierEndpointInterval_noncritical hs).2.1) :
      zagierPathTransport b γ χ ∈
        zagierConjugateSummand (zagierEndpointInterval_noncritical hs).2.1 := by
    rw [hγeq]
    exact zagierPathTransport_mem_conjugateSummand b (complexCirclePath s) hγ₁ hγreg
      (zagierEndpointInterval_noncritical hs).2.1 (zagierEndpointInterval_noncritical hs).2.1 hχ
  let η := zagierEndpointPath hr hs
  let θ := zagierEndpointPath hr ht
  have hH (u : ℝ) (hu : u ∈ Ioo 0 (1 / 9 : ℝ)) : AnalyticAt ℂ zagierAnalytic (u : ℂ) :=
    (zagierEndpointInterval_solutions hu).1
  have hHE (u : ℝ) (hu : u ∈ Ioo 0 (1 / 9 : ℝ)) :
      zagierSecondOrderODE zagierAnalytic =ᶠ[𝓝 (u : ℂ)] 0 :=
    (zagierEndpointInterval_solutions hu).2.1
  have hS (u : ℝ) (hu : u ∈ Ioo 0 (1 / 9 : ℝ)) :
      AnalyticAt ℂ zagierEndpointSolution (u : ℂ) :=
    (zagierEndpointInterval_solutions hu).2.2.1
  have hSE (u : ℝ) (hu : u ∈ Ioo 0 (1 / 9 : ℝ)) :
      zagierSecondOrderODE zagierEndpointSolution =ᶠ[𝓝 (u : ℂ)] 0 :=
    (zagierEndpointInterval_solutions hu).2.2.2
  obtain ⟨hγφ, hγψ⟩ := hγ (zagierPathTransport b η φ) (zagierPathTransport b η ψ)
    (mobiusGermPullback_zagierEndpointPath b hr hs hH hHE φ hφ)
    (mobiusGermPullback_zagierEndpointPath b hr hs hS hSE ψ hψ)
  obtain ⟨hδφ, hδψ⟩ := hδ (zagierPathTransport b θ φ) (zagierPathTransport b θ ψ)
    (mobiusGermPullback_zagierEndpointPath b hr ht hH hHE φ hφ)
    (mobiusGermPullback_zagierEndpointPath b hr ht hS hSE ψ hψ)
  refine ⟨(η.trans γ).trans η.symm, (θ.trans δ).trans θ.symm,
    k, l, hk, hl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [zagierPathTransport_trans, zagierPathTransport_trans, hγφ, zagierPathTransport_symm]
  · rw [zagierPathTransport_trans, zagierPathTransport_trans, hγψ,
      zagierPathTransport_add, zagierPathTransport_smul,
      zagierPathTransport_symm, zagierPathTransport_symm]
  · rw [zagierPathTransport_trans, zagierPathTransport_trans, hδφ,
      zagierPathTransport_add, zagierPathTransport_smul,
      zagierPathTransport_symm, zagierPathTransport_symm]
  · rw [zagierPathTransport_trans, zagierPathTransport_trans, hδψ, zagierPathTransport_symm]
  · intro χ hχ
    rw [zagierPathTransport_trans, zagierPathTransport_trans]
    have hmid := hγC _ ((zagierPathTransport_zagierEndpointPath_mem_conjugate_iff b hr hs χ).mpr hχ)
    apply (zagierPathTransport_zagierEndpointPath_mem_conjugate_iff b hr hs _).mp
    have hback : zagierPathTransport b η
        (zagierPathTransport b η.symm (zagierPathTransport b γ (zagierPathTransport b η χ))) =
        zagierPathTransport b γ (zagierPathTransport b η χ) := by
      simpa only [Path.symm_symm] using zagierPathTransport_symm b η.symm
        (zagierPathTransport b γ (zagierPathTransport b η χ))
    rw [hback]
    exact hmid
  · intro χ hχ
    rw [zagierPathTransport_trans, zagierPathTransport_trans]
    rw [hδC _ ((zagierPathTransport_zagierEndpointPath_mem_conjugate_iff b hr ht χ).mpr hχ),
      zagierPathTransport_symm]

end DirichletL
