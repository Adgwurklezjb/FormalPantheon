import Analysis.ZagierLogarithmicBasis
import Analysis.ZagierLogarithmicContinuation

/-!
The actual endpoint solution has nontrivial continuation around zero.
This supplies concrete monodromy data for CDT v2, Lemma `14functions`.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

theorem zagierSecondOrderODE_linearCombination {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (a b : ℂ) :
    zagierSecondOrderODE (fun w => a * f w + b * g w) z =
      a * zagierSecondOrderODE f z + b * zagierSecondOrderODE g z := by
  have hd : deriv (fun w => a * f w + b * g w) =ᶠ[𝓝 z]
      fun w => a * deriv f w + b * deriv g w := by
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with w hwf hwg
    exact ((hwf.differentiableAt.hasDerivAt.const_mul a).fun_add
      (hwg.differentiableAt.hasDerivAt.const_mul b)).deriv
  have hdd := (hf.deriv.differentiableAt.hasDerivAt.const_mul a).fun_add
    (hg.deriv.differentiableAt.hasDerivAt.const_mul b)
  rw [zagierSecondOrderODE, hd.deriv_eq, hdd.deriv, hd.self_of_nhds]
  dsimp [zagierSecondOrderODE]
  ring

theorem zagierSecondOrderODE_const_mul {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (a : ℂ) :
    zagierSecondOrderODE (fun w => a * f w) z = a * zagierSecondOrderODE f z := by
  simpa only [zero_mul, add_zero] using
    zagierSecondOrderODE_linearCombination (g := fun _ => 0) hf analyticAt_const a 0

theorem exists_zagierEndpointSolution_continuation_lt {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, r ∈ Ioo 0 (1 / 9 : ℝ) ∧ r < R ∧ ∃ b : ℂ, b ≠ 0 ∧ ∃ f : I → ℂ → ℂ,
      AnalyticContinuationAlong (complexCirclePath r) f ∧
        (∀ t : I, zagierSecondOrderODE (f t) =ᶠ[𝓝 (complexCirclePath r t)] 0) ∧
          f 0 =ᶠ[𝓝 (r : ℂ)] zagierEndpointSolution ∧
            (f 1 =ᶠ[𝓝 (r : ℂ)] fun z =>
              zagierEndpointSolution z + b * (2 * Real.pi * Complex.I) * zagierAnalytic z) ∧
                ¬f 0 =ᶠ[𝓝 (r : ℂ)] f 1 := by
  obtain ⟨ε, hε, hε₉, hεc⟩ := exists_zagierLogarithmicContinuation_radius
  have hex : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r ∧ r < ε ∧ r < R ∧ ∃ a b : ℂ, b ≠ 0 ∧
      zagierEndpointSolution =ᶠ[𝓝 (r : ℂ)] fun z =>
        a * zagierAnalytic z + b * zagierLogarithmicSolution z := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r : ℝ in 𝓝 0, r < ε from Iio_mem_nhds hε).filter_mono nhdsWithin_le_nhds,
      (show ∀ᶠ r : ℝ in 𝓝 0, r < R from Iio_mem_nhds hR).filter_mono nhdsWithin_le_nhds,
      eventually_zagierEndpointSolution_logarithmic.filter_mono nhdsWithin_le_nhds]
      with r hr hrε hrR hrc
    exact ⟨hr, hrε, hrR, hrc hr⟩
  obtain ⟨r, hr, hrε, hrR, a, b, hb, hab⟩ := hex.exists
  have hr₉ : r < 1 / 9 := lt_of_lt_of_le hrε hε₉
  obtain ⟨hc, hco, _⟩ := hεc r hr hrε
  have hnorm (t : I) : ‖complexCirclePath r t‖ < 1 / 9 := by
    simpa only [complexCirclePath_apply, norm_circleMap_zero, abs_of_pos hr] using hr₉
  let F : I → ℂ → ℂ := fun t z =>
    a * zagierAnalytic z + b * zagierLogarithmicContinuation r t z
  have hH := AnalyticContinuationAlong.const (complexCirclePath r).continuous
    (fun t => analyticAt_zagierAnalytic (hnorm t))
  have ha : AnalyticContinuationAlong (complexCirclePath r) (fun _ _ => a) :=
    AnalyticContinuationAlong.const (complexCirclePath r).continuous (fun _ => analyticAt_const)
  have hb' : AnalyticContinuationAlong (complexCirclePath r) (fun _ _ => b) :=
    AnalyticContinuationAlong.const (complexCirclePath r).continuous (fun _ => analyticAt_const)
  have hF : AnalyticContinuationAlong (complexCirclePath r) F :=
    (ha.mul hH).add (hb'.mul hc)
  have hFo (t : I) : zagierSecondOrderODE (F t) =ᶠ[𝓝 (complexCirclePath r t)] 0 := by
    filter_upwards [(analyticAt_zagierAnalytic (hnorm t)).eventually_analyticAt,
      (hc.analytic t).eventually_analyticAt, hco t,
      continuous_norm.continuousAt.eventually_lt_const (hnorm t)] with z hzH hzL hzLo hz
    change zagierSecondOrderODE (fun w => a * zagierAnalytic w +
      b * zagierLogarithmicContinuation r t w) z = 0
    rw [zagierSecondOrderODE_linearCombination hzH hzL]
    simp only [show zagierSecondOrderODE zagierAnalytic z = 0 from zagierAnalytic_ode hz,
      hzLo, Pi.zero_apply, mul_zero, add_zero]
  have hF₀ : F 0 =ᶠ[𝓝 (r : ℂ)] zagierEndpointSolution := by
    filter_upwards [hab, eventuallyEq_zagierLogarithmicContinuation_zero hr] with z hz hL
    dsimp [F]
    rw [hL]
    exact hz.symm
  have hF₁ : F 1 =ᶠ[𝓝 (r : ℂ)] fun z =>
      zagierEndpointSolution z + b * (2 * Real.pi * Complex.I) * zagierAnalytic z := by
    filter_upwards [hF₀] with z hz
    rw [← hz]
    dsimp [F]
    rw [zagierLogarithmicContinuation_one]
    ring
  refine ⟨r, ⟨hr, hr₉⟩, hrR, b, hb, F, hF, hFo, hF₀, hF₁, ?_⟩
  intro he
  have h := ((hF₀.symm.trans he).trans hF₁).eq_of_nhds
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hk : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero
  have hHr : zagierAnalytic (r : ℂ) ≠ 0 := by
    intro hz
    have hpos := one_le_zagierReal hr.le hr₉
    norm_num [zagierReal, hz] at hpos
  exact mul_ne_zero (mul_ne_zero hb hk) hHr (by linear_combination -h)

theorem exists_zagierEndpointSolution_continuation :
    ∃ r : ℝ, r ∈ Ioo 0 (1 / 9 : ℝ) ∧ ∃ b : ℂ, b ≠ 0 ∧ ∃ f : I → ℂ → ℂ,
      AnalyticContinuationAlong (complexCirclePath r) f ∧
        (∀ t : I, zagierSecondOrderODE (f t) =ᶠ[𝓝 (complexCirclePath r t)] 0) ∧
          f 0 =ᶠ[𝓝 (r : ℂ)] zagierEndpointSolution ∧
            (f 1 =ᶠ[𝓝 (r : ℂ)] fun z =>
              zagierEndpointSolution z + b * (2 * Real.pi * Complex.I) * zagierAnalytic z) ∧
                ¬f 0 =ᶠ[𝓝 (r : ℂ)] f 1 := by
  obtain ⟨r, hr, _, b, hb, f, hf, hE, h₀, h₁, hne⟩ :=
    exists_zagierEndpointSolution_continuation_lt (R := 1) (by norm_num)
  exact ⟨r, hr, b, hb, f, hf, hE, h₀, h₁, hne⟩

end DirichletL
