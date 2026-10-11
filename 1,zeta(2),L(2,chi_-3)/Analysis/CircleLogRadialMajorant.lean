import Analysis.CircleRadialLogBounds
import Analysis.AnalyticLogFactorBound
import Analysis.CircleLogIntegrability

/-!
Uniform radial domination for CDT v2, supplied TeX 4150-4153.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace DirichletL

theorem exists_circleLogProfile_radial_majorant {ψ : ℂ → ℂ}
    (hψ : AnalyticOnNhd ℂ ψ (Metric.closedBall 0 1)) (hderiv : deriv ψ 0 ≠ 0) :
    ∃ B : ℝ → ℝ, Integrable B (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0 : ℝ) 1),
        |circleLogProfile (fun z => ψ ((r : ℂ) * z)) t| ≤ B t := by
  classical
  let K : Set ℂ := Metric.sphere 0 1
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  let u (t : ℝ) : ℂ := fourier 1 (t : AddCircle (1 : ℝ))
  have hunorm (t : ℝ) : ‖u t‖ = 1 := Circle.norm_coe _
  have hnorm (a : K) : ‖(a : ℂ)‖ = 1 := by
    simpa only [K, Metric.mem_sphere, dist_zero_right] using a.property
  have hmem (a : K) : (a : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hnorm a]
  have hnot : ¬EqOn ψ 0 (Metric.closedBall (0 : ℂ) 1) := by
    intro hz
    have he : ψ =ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hzball
      exact hz (Metric.ball_subset_closedBall hzball)
    exact hderiv (by simpa only [deriv_const] using he.deriv_eq)
  have hgerm (a : K) : ¬∀ᶠ z in 𝓝 (a : ℂ), ψ z = 0 := by
    intro hz
    exact hnot (hψ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall (0 : ℂ) 1).isPreconnected (hmem a) hz)
  choose n δ C hδ hC hlocal using
    fun a : K => exists_local_analytic_log_factor_bound (hψ a (hmem a)) (hgerm a)
  let U (a : K) : Set ℂ := Metric.ball (a : ℂ) (δ a / 2)
  have hcover : K ⊆ ⋃ a : K, U a := by
    intro z hz
    apply Set.mem_iUnion.mpr
    exact ⟨⟨z, hz⟩, Metric.mem_ball_self (div_pos (hδ ⟨z, hz⟩) (by norm_num))⟩
  obtain ⟨S, hS⟩ := (isCompact_sphere (0 : ℂ) 1).elim_finite_subcover U
    (fun _ => Metric.isOpen_ball) hcover
  let B (t : ℝ) : ℝ := ∑ a ∈ S,
    (C a + (n a : ℝ) * (Real.log 2 + |Real.log ‖u t - (a : ℂ)‖|))
  have hB : Integrable B μ := by
    apply integrable_finset_sum
    intro a _
    have hlinear : IntervalIntegrable (fun t : ℝ => Real.log ‖u t - (a : ℂ)‖) volume 0 1 := by
      simpa only [circleLogProfile, u] using intervalIntegrable_circleLogProfile
        (ψ := fun z => z - (a : ℂ)) (fun _ _ => analyticAt_id.sub analyticAt_const)
    exact (integrable_const (C a)).add
      (((integrable_const (Real.log 2)).add hlinear.1.abs).const_mul (n a : ℝ))
  have hterm (a : K) (t : ℝ) :
      0 ≤ C a + (n a : ℝ) * (Real.log 2 + |Real.log ‖u t - (a : ℂ)‖|) :=
    add_nonneg (hC a) (mul_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Real.log_nonneg (by norm_num)) (abs_nonneg _)))
  have havoid : ∀ᵐ t : ℝ ∂μ, ∀ a ∈ S, u t ≠ (a : ℂ) := by
    apply S.finite_toSet.eventually_all.mpr
    intro a _
    exact ae_fourier_one_ne_on_unitInterval (a : ℂ)
  have hsmall : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ a ∈ S, |r - 1| < δ a / 2 := by
    apply S.finite_toSet.eventually_all.mpr
    intro a _
    have hc : ContinuousAt (fun r : ℝ => |r - 1|) 1 :=
      (continuous_id.sub continuous_const).abs.continuousAt
    have ht : Tendsto (fun r : ℝ => |r - 1|) (𝓝[<] 1) (𝓝 0) := by
      simpa only [sub_self, abs_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    exact ht.eventually (eventually_lt_nhds (div_pos (hδ a) (by norm_num)))
  have hhalf : ∀ᶠ r : ℝ in 𝓝[<] 1, (1 / 2 : ℝ) ≤ r := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)).filter_mono
      nhdsWithin_le_nhds] with r hr
    exact hr.le
  refine ⟨B, hB, ?_⟩
  filter_upwards [hsmall, hhalf, self_mem_nhdsWithin] with r hr hhalf hr1
  change r < 1 at hr1
  have hr0 : 0 ≤ r := by linarith only [hhalf]
  filter_upwards [havoid] with t ht
  have huK : u t ∈ K := by simp only [K, Metric.mem_sphere, dist_zero_right, hunorm]
  obtain ⟨a, haS, hua⟩ := Set.mem_iUnion₂.mp (hS huK)
  have hdist : dist ((r : ℂ) * u t) (u t) = |r - 1| := by
    rw [dist_eq_norm,
      show (r : ℂ) * u t - u t = ((r - 1 : ℝ) : ℂ) * u t by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, hunorm, mul_one]
  have hinside : (r : ℂ) * u t ∈ Metric.ball (a : ℂ) (δ a) := by
    rw [Metric.mem_ball]
    have huclose : dist (u t) (a : ℂ) < δ a / 2 := hua
    have htriangle := dist_triangle ((r : ℂ) * u t) (u t) (a : ℂ)
    rw [hdist] at htriangle
    linarith only [htriangle, hr a haS, huclose]
  have hpoint : (r : ℂ) * u t ≠ (a : ℂ) := by
    intro he
    have hn := congrArg norm he
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      hunorm, hnorm, mul_one] at hn
    linarith only [hn, hr1]
  have hlocalbound := hlocal a ((r : ℂ) * u t) hinside hpoint
  have hgeometry := abs_log_norm_radial_sub_le (hunorm t) (hnorm a) (ht a haS) hhalf hr1.le
  change |Real.log ‖ψ ((r : ℂ) * u t)‖| ≤ B t
  calc
    _ ≤ (n a : ℝ) * |Real.log ‖(r : ℂ) * u t - (a : ℂ)‖| + C a := hlocalbound
    _ ≤ (n a : ℝ) * (Real.log 2 + |Real.log ‖u t - (a : ℂ)‖|) + C a :=
      add_le_add_right (mul_le_mul_of_nonneg_left hgeometry (Nat.cast_nonneg _)) _
    _ = C a + (n a : ℝ) * (Real.log 2 + |Real.log ‖u t - (a : ℂ)‖|) := by ring
    _ ≤ B t := Finset.single_le_sum (fun b _ => hterm b t) haS

end DirichletL
