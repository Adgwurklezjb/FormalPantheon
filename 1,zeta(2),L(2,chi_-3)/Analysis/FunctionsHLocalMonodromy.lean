import Analysis.ZagierForcedWronskian
import Analysis.ZagierLocalCircles
import Analysis.ComplexLogarithmPeriods
import Analysis.FunctionsGContinuation

/-!
Actual nontrivial local continuations of the forced equation in CDT v2,
Proposition `functionsH`. The two Wronskian periods detect b and c and
provide local input for the nonzero-branch step of Lemma `14functions`.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

/-- Nonzero constant forcing produces nontrivial continuation on actual reciprocal circles. -/
theorem exists_forcedH_reciprocalCircle_nontrivial (b c : ℂ) (hb : b ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      ∃ γ : C(I, zagierPullbackRegularSet),
        (∀ t, (γ t : ℂ) = zagierReciprocalCoordinate (complexCirclePath r t)) ∧ γ 1 = γ 0 ∧
        ∀ H : ℂ → ℂ, AnalyticAt ℂ H (γ 0 : ℂ) →
          (∀ᶠ z in 𝓝 (γ 0 : ℂ), zagierSecondOrderODE H z = b + c / (1 - z)) →
          ∃ F : I → ℂ → ℂ,
            AnalyticContinuationAlong (fun t => (γ t : ℂ)) F ∧
            F 0 =ᶠ[𝓝 (γ 0 : ℂ)] H ∧
            (∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), zagierSecondOrderODE (F t) z = b + c / (1 - z)) ∧
            ¬F 1 =ᶠ[𝓝 (γ 0 : ℂ)] F 0 := by
  have hqinj : Function.Injective zagierReciprocalCoordinate := by
    intro z w he
    simpa only [zagierReciprocalCoordinate_self] using congrArg zagierReciprocalCoordinate he
  obtain ⟨R, hR, hcircle⟩ := exists_zagierRegularCircle_of_injective
    zagierReciprocalCoordinate hqinj (fun _ hz => analyticAt_zagierReciprocalCoordinate hz)
  obtain ⟨S, hS, hperiod⟩ := exists_radius_analyticContinuationAlong_deriv_ne
    (analyticAt_zagierInfinityRemainder_zero b c)
  refine ⟨min R (min S (1 / 9)), lt_min hR (lt_min hS (by norm_num)), ?_⟩
  intro r hr hrε
  obtain ⟨hrR, hrS, hrA⟩ := (lt_min_iff.mp hrε).imp_right lt_min_iff.mp
  obtain ⟨γ, hγ, hloop⟩ := hcircle r hr hrR
  refine ⟨γ, hγ, hloop, ?_⟩
  intro H hH hHo
  let δ : C(I, hForcedRegularSet) := {
    toFun t := ⟨(γ t : ℂ), mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet (γ t).property⟩
    continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _ }
  obtain ⟨F, hF, hF0, hFo⟩ := exists_analyticContinuationAlong_forcedH δ H b c hH hHo
  change AnalyticContinuationAlong (fun t => (γ t : ℂ)) F at hF
  change (∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), zagierSecondOrderODE (F t) z = b + c / (1 - z)) at hFo
  refine ⟨F, hF, hF0, hFo, ?_⟩
  have hn (t : I) : complexCirclePath r t ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_complexCirclePath, abs_of_pos hr]
    exact hr.ne'
  have hA : AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun _ => zagierInfinitySolution) := by
    apply AnalyticContinuationAlong.const (continuous_subtype_val.comp γ.continuous)
    intro t
    change AnalyticAt ℂ zagierInfinitySolution (γ t : ℂ)
    rw [hγ t]
    apply analyticAt_zagierInfinitySolution (zagierReciprocalCoordinate_ne_zero (hn t))
    simpa only [zagierReciprocalCoordinate_self, norm_complexCirclePath, abs_of_pos hr] using hrA
  have hW : AnalyticContinuationAlong (complexCirclePath r)
      (fun t z => zagierWeightedWronskian zagierInfinitySolution (F t)
        (zagierReciprocalCoordinate z)) :=
    (hA.zagierWeightedWronskian hF).comp (φ := zagierReciprocalCoordinate)
      (complexCirclePath r).continuous (fun t => analyticAt_zagierReciprocalCoordinate (hn t))
      (fun t => (hγ t).symm)
  have hWd (t : I) : ∀ᶠ z in 𝓝 (complexCirclePath r t),
      HasDerivAt (fun s => zagierWeightedWronskian zagierInfinitySolution (F t)
        (zagierReciprocalCoordinate s)) (-b / z + zagierInfinityRemainder b c z) z := by
    have ht := (analyticAt_zagierReciprocalCoordinate (hn t)).continuousAt.tendsto
    have hHa : AnalyticAt ℂ (F t) (zagierReciprocalCoordinate (complexCirclePath r t)) := by
      simpa only [hγ t] using hF.analytic t
    have hO : ∀ᶠ z in 𝓝 (zagierReciprocalCoordinate (complexCirclePath r t)),
        zagierSecondOrderODE (F t) z = b + c / (1 - z) := by
      simpa only [hγ t] using hFo t
    have hnorm : ‖complexCirclePath r t‖ < 1 / 9 := by
      simpa only [norm_complexCirclePath, abs_of_pos hr] using hrA
    filter_upwards [eventually_ne_nhds (hn t),
      continuous_norm.continuousAt.eventually_lt_const hnorm,
      ht.eventually hHa.eventually_analyticAt, ht.eventually hO] with z hz hzn hH hzO
    exact hasDerivAt_zagierWeightedWronskian_reciprocal hz hzn hH hzO
  have hne := hperiod r hr hrS (-b) (neg_ne_zero.mpr hb) _ hW hWd
  intro he
  have hwe : zagierWeightedWronskian zagierInfinitySolution (F 1) =ᶠ[𝓝 (γ 0 : ℂ)]
      zagierWeightedWronskian zagierInfinitySolution (F 0) := by
    filter_upwards [he, he.deriv] with z hz hzd
    simp only [zagierWeightedWronskian, hz, hzd]
  have hγ0 : (γ 0 : ℂ) = zagierReciprocalCoordinate (r : ℂ) := by
    simpa only [Path.source] using hγ 0
  have ht0 : Tendsto zagierReciprocalCoordinate (𝓝 (r : ℂ)) (𝓝 (γ 0 : ℂ)) := by
    rw [hγ0]
    exact (analyticAt_zagierReciprocalCoordinate (by exact_mod_cast hr.ne')).continuousAt.tendsto
  exact hne (hwe.comp_tendsto ht0)

/-- Nonzero pole forcing produces nontrivial continuation on actual circles around one. -/
theorem exists_forcedH_oneCircle_nontrivial (b c : ℂ) (hc : c ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      ∃ γ : C(I, zagierPullbackRegularSet),
        (∀ t, (γ t : ℂ) = 1 + complexCirclePath r t) ∧ γ 1 = γ 0 ∧
        ∀ H : ℂ → ℂ, AnalyticAt ℂ H (γ 0 : ℂ) →
          (∀ᶠ z in 𝓝 (γ 0 : ℂ), zagierSecondOrderODE H z = b + c / (1 - z)) →
          ∃ F : I → ℂ → ℂ,
            AnalyticContinuationAlong (fun t => (γ t : ℂ)) F ∧
            F 0 =ᶠ[𝓝 (γ 0 : ℂ)] H ∧
            (∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), zagierSecondOrderODE (F t) z = b + c / (1 - z)) ∧
            ¬F 1 =ᶠ[𝓝 (γ 0 : ℂ)] F 0 := by
  obtain ⟨R, hR, hcircle⟩ := exists_zagierRegularCircle_of_injective
    (fun z : ℂ => 1 + z) (fun _ _ he => add_left_cancel he) (fun _ _ => by fun_prop)
  obtain ⟨S, hS, hperiod⟩ := exists_radius_analyticContinuationAlong_deriv_ne
    (analyticAt_zagierOneRemainder_zero b c)
  have ht : Tendsto (fun z : ℂ => 1 + z) (𝓝 0) (𝓝 1) := by
    simpa using (show ContinuousAt (fun z : ℂ => 1 + z) 0 by fun_prop).tendsto
  obtain ⟨T, hT, hball⟩ := Metric.mem_nhds_iff.mp (ht.eventually
    (analyticAt_zagierOneSolution_one.eventually_analyticAt.and eventually_zagierOneSolution_ode))
  refine ⟨min R (min S T), lt_min hR (lt_min hS hT), ?_⟩
  intro r hr hrε
  obtain ⟨hrR, hrS, hrT⟩ := (lt_min_iff.mp hrε).imp_right lt_min_iff.mp
  obtain ⟨γ, hγ, hloop⟩ := hcircle r hr hrR
  refine ⟨γ, hγ, hloop, ?_⟩
  intro H hH hHo
  let δ : C(I, hForcedRegularSet) := {
    toFun t := ⟨(γ t : ℂ), mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet (γ t).property⟩
    continuous_toFun := (continuous_subtype_val.comp γ.continuous).subtype_mk _ }
  obtain ⟨F, hF, hF0, hFo⟩ := exists_analyticContinuationAlong_forcedH δ H b c hH hHo
  change AnalyticContinuationAlong (fun t => (γ t : ℂ)) F at hF
  change (∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), zagierSecondOrderODE (F t) z = b + c / (1 - z)) at hFo
  refine ⟨F, hF, hF0, hFo, ?_⟩
  have hm (t : I) : complexCirclePath r t ∈ Metric.ball (0 : ℂ) T := by
    simpa only [Metric.mem_ball, dist_zero_right, norm_complexCirclePath, abs_of_pos hr] using hrT
  have hn (t : I) : complexCirclePath r t ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_complexCirclePath, abs_of_pos hr]
    exact hr.ne'
  have hA : AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun _ => zagierOneSolution) := by
    apply AnalyticContinuationAlong.const (continuous_subtype_val.comp γ.continuous)
    intro t
    change AnalyticAt ℂ zagierOneSolution (γ t : ℂ)
    rw [hγ t]
    exact (hball (hm t)).1
  have hW : AnalyticContinuationAlong (complexCirclePath r)
      (fun t z => zagierWeightedWronskian zagierOneSolution (F t) (1 + z)) :=
    (hA.zagierWeightedWronskian hF).comp (φ := fun z => 1 + z)
      (complexCirclePath r).continuous (fun _ => by fun_prop) (fun t => (hγ t).symm)
  have hWd (t : I) : ∀ᶠ z in 𝓝 (complexCirclePath r t),
      HasDerivAt (fun s => zagierWeightedWronskian zagierOneSolution (F t) (1 + s))
        (-(c * (9 / 8)) / z + zagierOneRemainder b c z) z := by
    have ht := (show ContinuousAt (fun z : ℂ => 1 + z) (complexCirclePath r t) by fun_prop).tendsto
    have hHa : AnalyticAt ℂ (F t) (1 + complexCirclePath r t) := by
      simpa only [hγ t] using hF.analytic t
    have hO : ∀ᶠ z in 𝓝 (1 + complexCirclePath r t),
        zagierSecondOrderODE (F t) z = b + c / (1 - z) := by
      simpa only [hγ t] using hFo t
    filter_upwards [eventually_ne_nhds (hn t), Metric.isOpen_ball.mem_nhds (hm t),
      ht.eventually hHa.eventually_analyticAt, ht.eventually hO] with z hz hzm hH hzO
    exact hasDerivAt_zagierWeightedWronskian_one hz (hball hzm).1 (hball hzm).2 hH hzO
  have hk : -(c * (9 / 8 : ℂ)) ≠ 0 := neg_ne_zero.mpr (mul_ne_zero hc (by norm_num))
  have hne := hperiod r hr hrS (-(c * (9 / 8))) hk _ hW hWd
  intro he
  have hwe : zagierWeightedWronskian zagierOneSolution (F 1) =ᶠ[𝓝 (γ 0 : ℂ)]
      zagierWeightedWronskian zagierOneSolution (F 0) := by
    filter_upwards [he, he.deriv] with z hz hzd
    simp only [zagierWeightedWronskian, hz, hzd]
  have hγ0 : (γ 0 : ℂ) = 1 + (r : ℂ) := by simpa only [Path.source] using hγ 0
  have ht0 : Tendsto (fun z : ℂ => 1 + z) (𝓝 (r : ℂ)) (𝓝 (γ 0 : ℂ)) := by
    rw [hγ0]
    exact (show ContinuousAt (fun z : ℂ => 1 + z) (r : ℂ) by fun_prop).tendsto
  exact hne (hwe.comp_tendsto ht0)

end DirichletL
