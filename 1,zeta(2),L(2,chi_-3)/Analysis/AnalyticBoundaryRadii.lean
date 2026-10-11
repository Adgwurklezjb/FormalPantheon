import Mathlib

/-!
Common inner radii avoiding zeros, as used in CDT v2 TeX 4150-4153.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem finite_zeros_on_compact_of_analyticOnNhd {K : Set ℂ} {f : ℂ → ℂ}
    (hK : IsCompact K) (hconn : IsPreconnected K) (hf : AnalyticOnNhd ℂ f K)
    (hne : ¬Set.EqOn f 0 K) : {z | z ∈ K ∧ f z = 0}.Finite := by
  have hcod := (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hconn).resolve_left hne
  have hfinite : (K \ {z | f z ≠ 0}).Finite := by
    by_contra hinfinite
    obtain ⟨x, hx, hacc⟩ :=
      Set.Infinite.exists_accPt_of_subset_isCompact hinfinite hK (fun _ hz => hz.1)
    exact (mem_codiscreteWithin_accPt.mp hcod) x hx hacc
  convert hfinite using 1
  ext z
  simp

theorem eventually_sphere_ne_zero_of_finite_zeros {f : ℂ → ℂ}
    (hfinite : {z | z ∈ Metric.closedBall (0 : ℂ) 1 ∧ f z = 0}.Finite) :
    ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ z : ℂ, ‖z‖ = r → f z ≠ 0 := by
  have havoid : ∀ᶠ r : ℝ in 𝓝[<] 1,
      ∀ z ∈ {z | z ∈ Metric.closedBall (0 : ℂ) 1 ∧ f z = 0}, r ≠ ‖z‖ := by
    apply hfinite.eventually_all.mpr
    intro z _hz
    by_cases he : ‖z‖ = 1
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [he] using (ne_of_lt hr : r ≠ (1 : ℝ))
    · exact (eventually_ne_nhds (Ne.symm he)).filter_mono nhdsWithin_le_nhds
  filter_upwards [havoid, self_mem_nhdsWithin] with r hr hrl
  intro z hz hfz
  have hzK : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, hz] using hrl.le
  exact hr z ⟨hzK, hfz⟩ hz.symm

theorem eventually_family_sphere_ne_zero {ι : Type*} [Fintype ι]
    (ψ : ι → ℂ → ℂ)
    (hdψ : ∀ q, AnalyticOnNhd ℂ (ψ q) (Metric.closedBall 0 1))
    (hderiv : ∀ q, deriv (ψ q) 0 ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ q (z : ℂ), ‖z‖ = r → ψ q z ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro q
  apply eventually_sphere_ne_zero_of_finite_zeros
  apply finite_zeros_on_compact_of_analyticOnNhd (isCompact_closedBall (0 : ℂ) 1)
    (convex_closedBall (0 : ℂ) 1).isPreconnected (hdψ q)
  intro hzero
  have hlocal : ψ q =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    exact hzero (Metric.ball_subset_closedBall hz)
  exact hderiv q (by simpa only [deriv_const] using hlocal.deriv_eq)

end DirichletL
