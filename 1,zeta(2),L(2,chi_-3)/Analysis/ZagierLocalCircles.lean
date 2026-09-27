import Analysis.ZagierSheetPaths
import Analysis.ComplexLogarithmCircle

/-!
Actual small circles in the original coordinate, avoiding all punctures of
the descended Zagier equation. These give admissible forced continuations
for CDT v2, `functionsH` and the nonzero-branch step in `14functions`.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

theorem exists_radius_zagierPullbackRegular_of_injective (φ : ℂ → ℂ)
    (hφ : Function.Injective φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ < ε → φ z ∈ zagierPullbackRegularSet := by
  have hf : (φ ⁻¹' zagierPullbackRegularSetᶜ).Finite :=
    Set.Finite.preimage hφ.injOn finite_compl_zagierPullbackRegularSet
  have hn : (φ ⁻¹' zagierPullbackRegularSetᶜ)ᶜ ∈ 𝓝[≠] (0 : ℂ) := by
    have he := nhdNE_of_nhdNE_sdiff_finite
      (Filter.univ_mem : (Set.univ : Set ℂ) ∈ 𝓝[≠] (0 : ℂ)) hf
    filter_upwards [he] with z hz
    exact hz.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hn
  refine ⟨ε, hε, ?_⟩
  intro z hz hzε
  have hm : z ∈ (φ ⁻¹' zagierPullbackRegularSetᶜ)ᶜ := hball
    ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hzε, by simpa using hz⟩
  simpa only [mem_compl_iff, mem_preimage, not_not] using hm

/-- Injective coordinates analytic off zero send small circles to actual regular closed curves. -/
theorem exists_zagierRegularCircle_of_injective (φ : ℂ → ℂ) (hφ : Function.Injective φ)
    (ha : ∀ z : ℂ, z ≠ 0 → AnalyticAt ℂ φ z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      ∃ γ : C(I, zagierPullbackRegularSet),
        (∀ t, (γ t : ℂ) = φ (complexCirclePath r t)) ∧ γ 1 = γ 0 := by
  obtain ⟨ε, hε, hreg⟩ := exists_radius_zagierPullbackRegular_of_injective φ hφ
  refine ⟨ε, hε, ?_⟩
  intro r hr hrε
  have hn (t : I) : complexCirclePath r t ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_complexCirclePath, abs_of_pos hr]
    exact hr.ne'
  have hc : Continuous (fun t : I => φ (complexCirclePath r t)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (ha _ (hn t)).continuousAt.comp (complexCirclePath r).continuous.continuousAt)
  let γ : C(I, zagierPullbackRegularSet) := {
    toFun t := ⟨φ (complexCirclePath r t), hreg _ (hn t)
      (by simpa only [norm_complexCirclePath, abs_of_pos hr] using hrε)⟩
    continuous_toFun := hc.subtype_mk _ }
  refine ⟨γ, fun _ => rfl, ?_⟩
  apply Subtype.ext
  change φ (complexCirclePath r 1) = φ (complexCirclePath r 0)
  rw [Path.target, Path.source]

end DirichletL
