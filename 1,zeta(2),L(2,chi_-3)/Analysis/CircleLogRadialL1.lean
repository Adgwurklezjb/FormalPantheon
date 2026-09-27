import Analysis.CircleLogRadialMajorant
import Analysis.AnalyticBoundaryRadii

/-!
The actual logarithmic radial L1 limit in CDT v2, supplied TeX 4150-4153.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace DirichletL

theorem ae_circleProfile_argument_ne_zero {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.closedBall 0 1)) (hderiv : deriv ψ 0 ≠ 0) :
    ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0 : ℝ) 1),
      ψ (fourier 1 (t : AddCircle (1 : ℝ))) ≠ 0 := by
  have hnot : ¬EqOn ψ 0 (Metric.closedBall (0 : ℂ) 1) := by
    intro hz
    have he : ψ =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hzball
      exact hz (Metric.ball_subset_closedBall hzball)
    exact hderiv (by simpa only [deriv_const] using he.deriv_eq)
  have hfinite := finite_zeros_on_compact_of_analyticOnNhd (isCompact_closedBall (0 : ℂ) 1)
    (convex_closedBall (0 : ℂ) 1).isPreconnected hψ hnot
  have havoid : ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0 : ℝ) 1),
      ∀ a ∈ {z : ℂ | z ∈ Metric.closedBall 0 1 ∧ ψ z = 0},
        fourier 1 (t : AddCircle (1 : ℝ)) ≠ a :=
    hfinite.eventually_all.mpr (fun a _ => ae_fourier_one_ne_on_unitInterval a)
  filter_upwards [havoid] with t ht
  intro hzero
  have hu : fourier 1 (t : AddCircle (1 : ℝ)) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (Circle.norm_coe _)
  exact ht _ ⟨hu, hzero⟩ rfl

theorem tendsto_L1_circleLogProfile_radial {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.closedBall 0 1)) (hderiv : deriv ψ 0 ≠ 0) :
    Tendsto (fun r : ℝ => ∫ t in (0 : ℝ)..1,
      |circleLogProfile (fun z => ψ ((r : ℂ) * z)) t - circleLogProfile ψ t|)
      (𝓝[<] 1) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  obtain ⟨B, hB, hbound⟩ := exists_circleLogProfile_radial_majorant hψ hderiv
  have hbase := intervalIntegrable_circleLogProfile hψ
  have hproper : ∀ᶠ r : ℝ in 𝓝[<] 1, 0 < r ∧ r < 1 := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with r hr hr1
    exact ⟨hr, hr1⟩
  have hint : ∀ᶠ r : ℝ in 𝓝[<] 1,
      IntervalIntegrable (circleLogProfile (fun z => ψ ((r : ℂ) * z))) volume 0 1 := by
    filter_upwards [hproper] with r hr
    apply intervalIntegrable_circleLogProfile
    intro z hz
    have hscaled : (r : ℂ) * z ∈ Metric.closedBall (0 : ℂ) 1 := by
      have hz1 : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
      exact (mul_le_mul_of_nonneg_left hz1 hr.1.le).trans (by simpa only [mul_one] using hr.2.le)
    exact (hψ _ hscaled).comp' (analyticAt_const.mul analyticAt_id)
  have hmeas : ∀ᶠ r : ℝ in 𝓝[<] 1, AEStronglyMeasurable
      (fun t => |circleLogProfile (fun z => ψ ((r : ℂ) * z)) t - circleLogProfile ψ t|) μ := by
    filter_upwards [hint] with r hr
    exact (hr.sub hbase).abs.1.aestronglyMeasurable
  have hdom : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ᵐ t : ℝ ∂μ,
      ‖|circleLogProfile (fun z => ψ ((r : ℂ) * z)) t - circleLogProfile ψ t|‖ ≤
        B t + |circleLogProfile ψ t| := by
    filter_upwards [hbound] with r hr
    filter_upwards [hr] with t ht
    rw [Real.norm_eq_abs, abs_abs]
    exact (abs_sub _ _).trans (add_le_add_right ht _)
  have hlim : ∀ᵐ t : ℝ ∂μ, Tendsto
      (fun r : ℝ => |circleLogProfile (fun z => ψ ((r : ℂ) * z)) t - circleLogProfile ψ t|)
      (𝓝[<] 1) (𝓝 0) := by
    filter_upwards [ae_circleProfile_argument_ne_zero hψ hderiv] with t ht
    let u : ℂ := fourier 1 (t : AddCircle (1 : ℝ))
    have hu : u ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (Circle.norm_coe _)
    have hc : ContinuousAt (fun z => Real.log ‖ψ z‖) u :=
      (hψ u hu).continuousAt.norm.log (norm_ne_zero_iff.mpr ht)
    have hr : Tendsto (fun r : ℝ => (r : ℂ) * u) (𝓝[<] 1) (𝓝 u) := by
      simpa only [Complex.ofReal_one, one_mul] using
        ((Complex.continuous_ofReal.tendsto 1).mul_const u).mono_left nhdsWithin_le_nhds
    have hp : Tendsto (fun r : ℝ => circleLogProfile (fun z => ψ ((r : ℂ) * z)) t)
        (𝓝[<] 1) (𝓝 (circleLogProfile ψ t)) := hc.tendsto.comp hr
    simpa only [sub_self, abs_zero] using (hp.sub_const (circleLogProfile ψ t)).abs
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (f := fun _ : ℝ => (0 : ℝ)) (fun t => B t + |circleLogProfile ψ t|)
    hmeas hdom (hB.add hbase.1.abs) hlim
  simpa only [μ, integral_zero,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hdct

end DirichletL
