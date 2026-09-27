import Analysis.AnalyticLinearODESections
import Analysis.AnalyticLinearODESectionContinuity

/-!
Extension of a specified matrix solution through a regular homotopy.
Source: CDT v2 TeX 1739-1744 and 7157-7173. Prior meaning and overlap checks:
-/

namespace DirichletL.AnalyticMatrixODE

open Filter Bundle
open scoped Topology Matrix

variable {I : Type*} [Fintype I] (D : AnalyticMatrixODE I)

theorem exists_analytic_extension_of_homotopy (b : D.domain)
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → I → ℂ}
    (hf : AnalyticOnNhd ℂ f U)
    (hfo : ∀ z ∈ D.domain ∩ U, HasDerivAt f (D.matrix z *ᵥ f z) z)
    (H : C(unitInterval × D.domain, D.domain))
    (hzero : ∀ z, (H (0, z) : ℂ) ∈ U)
    (hone : ∀ z, H (1, z) = z)
    (hstay : ∀ t (z : D.domain), (z : ℂ) ∈ U → (H (t, z) : ℂ) ∈ U) :
    ∃ g : ℂ → I → ℂ, AnalyticOnNhd ℂ g (U ∪ D.domain) ∧ Set.EqOn g f U ∧
      ∀ z ∈ D.domain, HasDerivAt g (D.matrix z *ᵥ g z) z := by
  classical
  have hlocal (z : D.domain) (hz : (z : ℂ) ∈ U) :
      ∀ᶠ w in 𝓝 (z : ℂ), HasDerivAt f (D.matrix w *ᵥ f w) w := by
    filter_upwards [(D.isOpen_domain.inter hU).mem_nhds ⟨z.property, hz⟩] with w hw
    exact hfo w hw
  let v (z : D.domain) (hz : (z : ℂ) ∈ U) : D.Continuation b :=
    ⟨z, D.solutionGermOfFun f (hf z hz) (hlocal z hz)⟩
  let u₀ : C(D.domain, D.Continuation b) :=
    ⟨fun z => v (H (0, z)) (hzero z), by
      apply D.continuous_continuation_of_representative b (f := f)
      · exact H.continuous.comp (continuous_const.prodMk continuous_id)
      · intro z
        rfl⟩
  let cov := D.isCoveringMap_continuationProjection b
  have hstart (z : D.domain) : H (0, z) = D.continuationProjection b (u₀ z) := rfl
  let u := cov.liftHomotopy H u₀ hstart
  have hp (t : unitInterval) (z : D.domain) : (u (t, z)).proj = H (t, z) :=
    congrFun (cov.liftHomotopy_lifts H u₀ hstart) (t, z)
  have hu₁ : Continuous (fun z => u (1, z)) :=
    u.continuous.comp (continuous_const.prodMk continuous_id)
  have hp₁ (z : D.domain) : (u (1, z)).proj = z := (hp 1 z).trans (hone z)
  obtain ⟨F, hFa, hFo, hFrep⟩ :=
    D.exists_analytic_representative_of_continuation_section b hu₁ hp₁
  have hagree (z : D.domain) (hz : (z : ℂ) ∈ U) : F z = f z := by
    let vpath (t : unitInterval) : D.Continuation b :=
      v (H (t, z)) (hstay t z hz)
    have hvpath : Continuous vpath := by
      apply D.continuous_continuation_of_representative b (f := f)
      · exact H.continuous.comp (continuous_id.prodMk continuous_const)
      · intro t
        rfl
    have he : (fun t => u (t, z)) = vpath := by
      apply cov.eq_of_comp_eq
        (u.continuous.comp (continuous_id.prodMk continuous_const)) hvpath
        (funext fun t => hp t z) 0
      exact cov.liftHomotopy_zero H u₀ hstart z
    have he₁ : u (1, z) = v z hz := by
      calc
        u (1, z) = vpath 1 := congrFun he 1
        _ = v z hz := by simp only [vpath, hone z]
    have h := hFrep z
    rw [he₁] at h
    have hlocal : f =ᶠ[𝓝 (z : ℂ)] F := Germ.coe_eq.mp h
    exact hlocal.self_of_nhds.symm
  let g (z : ℂ) := if z ∈ U then f z else F z
  have hgU : Set.EqOn g f U := fun z hz => if_pos hz
  have hgD : Set.EqOn g F D.domain := by
    intro z hz
    dsimp only [g]
    split_ifs with h
    · exact (hagree ⟨z, hz⟩ h).symm
    · rfl
  have hnearU (z : ℂ) (hz : z ∈ U) : g =ᶠ[𝓝 z] f := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact hgU hw
  have hnearD (z : ℂ) (hz : z ∈ D.domain) : g =ᶠ[𝓝 z] F := by
    filter_upwards [D.isOpen_domain.mem_nhds hz] with w hw
    exact hgD hw
  refine ⟨g, ?_, hgU, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · exact (hf z hz).congr (hnearU z hz).symm
    · exact (hFa z hz).congr (hnearD z hz).symm
  · intro z hz
    simpa only [hgD hz] using (hFo z hz).congr_of_eventuallyEq (hnearD z hz)

end DirichletL.AnalyticMatrixODE
