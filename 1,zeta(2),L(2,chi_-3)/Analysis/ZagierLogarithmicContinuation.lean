import Analysis.ComplexLogarithmCircle
import Analysis.ZagierLogarithm

/-!
Actual logarithmic continuation once around a sufficiently small circle
for CDT v2 equation `zagr`, supplying local monodromy data for `14functions`.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

/-- The Zagier logarithmic solution using a branch based in the exponential coordinate. -/
noncomputable def zagierLogarithmicBranch (w z : ℂ) : ℂ :=
  zagierAnalytic z * (complexLogarithmBranch w z + zagierLogarithmCorrection z)

theorem zagierLogarithmicBranch_add_period (w z : ℂ) :
    zagierLogarithmicBranch (w + 2 * Real.pi * Complex.I) z =
      zagierLogarithmicBranch w z + 2 * Real.pi * Complex.I * zagierAnalytic z := by
  simp only [zagierLogarithmicBranch, complexLogarithmBranch_add_period]
  ring

theorem eventually_zagierLogarithmicBranch :
    ∀ᶠ z in 𝓝 0, ∀ w : ℂ, z / Complex.exp w ∈ Complex.slitPlane →
      AnalyticAt ℂ (zagierLogarithmicBranch w) z ∧
        zagierSecondOrderODE (zagierLogarithmicBranch w) z = 0 ∧
          zagierWeightedWronskian zagierAnalytic (zagierLogarithmicBranch w) z = 1 := by
  filter_upwards [eventually_zagierLogarithmicProduct] with z hz
  intro w hs
  have hz₀ : z ≠ 0 := by
    intro he
    exact Complex.slitPlane_ne_zero hs (by simp [he])
  apply hz (complexLogarithmBranch w) hz₀ (analyticAt_complexLogarithmBranch hs)
  filter_upwards [(continuous_id.div_const (Complex.exp w)).continuousAt.preimage_mem_nhds
    (Complex.isOpen_slitPlane.mem_nhds hs)] with u hu
  exact hasDerivAt_complexLogarithmBranch hu

/-- Local representatives along the standard circle, with a continuously increasing logarithm. -/
noncomputable def zagierLogarithmicContinuation (r : ℝ) (t : I) : ℂ → ℂ :=
  zagierLogarithmicBranch (complexCircleLift r t)

@[simp] theorem zagierLogarithmicContinuation_zero (r : ℝ) :
    zagierLogarithmicContinuation r 0 = zagierLogarithmicBranch (Complex.log r) := by
  simp [zagierLogarithmicContinuation]

theorem zagierLogarithmicContinuation_one (r : ℝ) (z : ℂ) :
    zagierLogarithmicContinuation r 1 z =
      zagierLogarithmicContinuation r 0 z + 2 * Real.pi * Complex.I * zagierAnalytic z := by
  simp only [zagierLogarithmicContinuation, complexCircleLift_one, complexCircleLift_zero,
    zagierLogarithmicBranch_add_period]

theorem eventuallyEq_zagierLogarithmicContinuation_zero {r : ℝ} (hr : 0 < r) :
    zagierLogarithmicContinuation r 0 =ᶠ[𝓝 (r : ℂ)] zagierLogarithmicSolution := by
  filter_upwards [eventuallyEq_complexLogarithmBranch_log_ofReal hr] with z hz
  simp only [zagierLogarithmicContinuation_zero, zagierLogarithmicBranch,
    zagierLogarithmicSolution, hz]

theorem exists_zagierLogarithmicContinuation_radius :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 9 ∧ ∀ r : ℝ, 0 < r → r < ε →
      AnalyticContinuationAlong (complexCirclePath r) (zagierLogarithmicContinuation r) ∧
        (∀ t : I, zagierSecondOrderODE (zagierLogarithmicContinuation r t) =ᶠ[
          𝓝 (complexCirclePath r t)] 0) ∧
          ¬zagierLogarithmicContinuation r 0 =ᶠ[𝓝 (r : ℂ)] zagierLogarithmicContinuation r 1 := by
  have hH : AnalyticAt ℂ zagierAnalytic 0 := analyticAt_zagierAnalytic (by norm_num)
  have hHne : ∀ᶠ z in 𝓝 0, zagierAnalytic z ≠ 0 :=
    hH.continuousAt.eventually_ne (by rw [zagierAnalytic_zero]; norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hH.eventually_analyticAt.and
    (analyticAt_zagierLogarithmCorrection_zero.eventually_analyticAt.and
      (hHne.and eventually_zagierLogarithmicBranch.eventually_nhds)))
  refine ⟨min ε (1 / 9), lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro r hr hrε
  have hrε' : r < ε := lt_of_lt_of_le hrε (min_le_left _ _)
  have hm (t : I) : complexCirclePath r t ∈ Metric.ball (0 : ℂ) ε := by
    simpa only [Metric.mem_ball, dist_zero_right, complexCirclePath_apply,
      norm_circleMap_zero, abs_of_pos hr] using hrε'
  refine ⟨?_, ?_, ?_⟩
  · have hHC := AnalyticContinuationAlong.const (complexCirclePath r).continuous
      (fun t => (hball (hm t)).1)
    have hBC := AnalyticContinuationAlong.const (complexCirclePath r).continuous
      (fun t => (hball (hm t)).2.1)
    have hlog : AnalyticContinuationAlong (complexCirclePath r)
        (fun t => complexLogarithmBranch (complexCircleLift r t)) := by
      simpa only [exp_complexCircleLift hr] using
        analyticContinuationAlong_complexLogarithmBranch (continuous_complexCircleLift r)
    exact hHC.mul (hlog.add hBC)
  · intro t
    have hs : complexCirclePath r t / Complex.exp (complexCircleLift r t) ∈ Complex.slitPlane := by
      rw [← exp_complexCircleLift hr t]
      simp [Complex.exp_ne_zero]
    have hd := (continuous_id.div_const (Complex.exp (complexCircleLift r t))).continuousAt
      (x := complexCirclePath r t)
    have hn := hd.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hs)
    filter_upwards [(hball (hm t)).2.2.2, hn] with z hz hzs
    exact (hz (complexCircleLift r t) hzs).2.1
  · intro he
    have h := he.eq_of_nhds
    rw [zagierLogarithmicContinuation_one] at h
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hk : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero
    have hn : zagierAnalytic (r : ℂ) ≠ 0 := by
      simpa only [Path.source] using (hball (hm 0)).2.2.1
    exact mul_ne_zero hk hn (by linear_combination -h)

theorem zagierLogarithmicContinuation_endpoint_of_initial {r : ℝ} (hr : 0 < r)
    (hc : AnalyticContinuationAlong (complexCirclePath r) (zagierLogarithmicContinuation r))
    {f : I → ℂ → ℂ} (hf : AnalyticContinuationAlong (complexCirclePath r) f)
    (hi : f 0 =ᶠ[𝓝 (r : ℂ)] zagierLogarithmicSolution) :
    f 1 =ᶠ[𝓝 (r : ℂ)] fun z =>
      zagierLogarithmicSolution z + 2 * Real.pi * Complex.I * zagierAnalytic z := by
  have hinit : f 0 =ᶠ[𝓝 (complexCirclePath r 0)] zagierLogarithmicContinuation r 0 := by
    simpa only [Path.source] using hi.trans (eventuallyEq_zagierLogarithmicContinuation_zero hr).symm
  have he := hf.eq_of_preconnectedSpace hc hinit 1
  simp only [Path.target] at he
  filter_upwards [he, eventuallyEq_zagierLogarithmicContinuation_zero hr] with z hz hzi
  rw [hz, zagierLogarithmicContinuation_one, hzi]

end DirichletL
