import Analysis.ZagierConjugateAnalytic

/-!
A uniform local analytic basis for the conjugate summand in CDT v2, `14functions`.
At its ordinary points, two initial states control every solution germ nearby.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem eventuallyEq_zagierConjugate_basis {f g h : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hh : AnalyticAt ℂ h z)
    (hz : z * (z - 1) ^ 2 * (8 * z + 1) ≠ 0)
    (hfo : zagierConjugateAnalyticODE f =ᶠ[𝓝 z] 0)
    (hgo : zagierConjugateAnalyticODE g =ᶠ[𝓝 z] 0)
    (hho : zagierConjugateAnalyticODE h =ᶠ[𝓝 z] 0)
    (hw : g z * deriv h z - deriv g z * h z ≠ 0) :
    ∃ a b : ℂ, f =ᶠ[𝓝 z] fun w => a * g w + b * h w := by
  let a := (f z * deriv h z - deriv f z * h z) / (g z * deriv h z - deriv g z * h z)
  let b := (g z * deriv f z - deriv g z * f z) / (g z * deriv h z - deriv g z * h z)
  let F : ℂ → ℂ := fun w => a * g w + b * h w
  have hF : AnalyticAt ℂ F z := (hg.const_smul (c := a)).add (hh.const_smul (c := b))
  have hFo : zagierConjugateAnalyticODE F =ᶠ[𝓝 z] 0 := by
    filter_upwards [hg.eventually_analyticAt, hh.eventually_analyticAt, hgo, hho]
      with w hgw hhw hge hhe
    simp only [F, zagierConjugateAnalyticODE_linearCombination hgw hhw,
      hge, hhe, Pi.zero_apply, mul_zero, add_zero]
  have hv : (f - F) z = 0 := by
    simp only [Pi.sub_apply, F, a, b]
    field_simp [hw]
    linear_combination -f z * (mul_inv_cancel₀ hw)
  have hd : deriv (f - F) z = 0 := by
    change deriv (fun w => f w - F w) z = 0
    rw [(hf.differentiableAt.hasDerivAt.fun_sub hF.differentiableAt.hasDerivAt).deriv,
      ((hg.differentiableAt.hasDerivAt.const_mul a).fun_add
        (hh.differentiableAt.hasDerivAt.const_mul b)).deriv]
    dsimp [a, b]
    field_simp [hw]
    linear_combination -deriv f z * (mul_inv_cancel₀ hw)
  have ho : zagierConjugateAnalyticODE (f - F) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hf.eventually_analyticAt, hF.eventually_analyticAt, hfo, hFo]
      with w hfw hFw hfe hFe
    simpa [sub_eq_add_neg, hfe, hFe] using
      zagierConjugateAnalyticODE_linearCombination hfw hFw 1 (-1)
  have he := eventuallyEq_zero_of_analytic_secondOrder_ode
    (a := fun w => w * (w - 1) ^ 2 * (8 * w + 1))
    (b := fun w => (w - 1) * (8 * w ^ 2 - 16 * w - 1)) (c := fun w => 3 * (2 * w + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) hz (hf.sub hF) hv hd ho
  refine ⟨a, b, ?_⟩
  filter_upwards [he] with w hw
  exact sub_eq_zero.mp hw

theorem exists_zagierConjugate_local_basis {z0 : ℂ}
    (hz0 : z0 * (z0 - 1) ^ 2 * (8 * z0 + 1) ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∃ g h : ℂ → ℂ, ∀ z ∈ Metric.ball z0 R,
      AnalyticAt ℂ g z ∧ AnalyticAt ℂ h z ∧
        zagierConjugateAnalyticODE g =ᶠ[𝓝 z] 0 ∧
        zagierConjugateAnalyticODE h =ᶠ[𝓝 z] 0 ∧
        g z * deriv h z - deriv g z * h z ≠ 0 ∧
        ∀ f : ℂ → ℂ, AnalyticAt ℂ f z → zagierConjugateAnalyticODE f =ᶠ[𝓝 z] 0 →
          ∃ a b : ℂ, f =ᶠ[𝓝 z] fun w => a * g w + b * h w := by
  obtain ⟨g, hg, hg₀, hg₁, hgo⟩ := exists_analytic_zagierConjugate_ode hz0 1 0
  obtain ⟨h, hh, hh₀, hh₁, hho⟩ := exists_analytic_zagierConjugate_ode hz0 0 1
  have hw : g z0 * deriv h z0 - deriv g z0 * h z0 ≠ 0 := by
    simp [hg₀, hg₁, hh₀, hh₁]
  have hc : ContinuousAt (fun z => g z * deriv h z - deriv g z * h z) z0 :=
    (hg.continuousAt.mul hh.deriv.continuousAt).sub (hg.deriv.continuousAt.mul hh.continuousAt)
  have ha : ContinuousAt (fun z : ℂ => z * (z - 1) ^ 2 * (8 * z + 1)) z0 := by fun_prop
  have hn : ∀ᶠ z in 𝓝 z0, AnalyticAt ℂ g z ∧ AnalyticAt ℂ h z ∧
      zagierConjugateAnalyticODE g =ᶠ[𝓝 z] 0 ∧
      zagierConjugateAnalyticODE h =ᶠ[𝓝 z] 0 ∧
      g z * deriv h z - deriv g z * h z ≠ 0 ∧ z * (z - 1) ^ 2 * (8 * z + 1) ≠ 0 := by
    filter_upwards [hg.eventually_analyticAt, hh.eventually_analyticAt,
      hgo.eventually_nhds, hho.eventually_nhds, hc.eventually_ne hw, ha.eventually_ne hz0]
      with z hg' hh' hgo' hho' hw' ha'
    exact ⟨hg', hh', hgo', hho', hw', ha'⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨R, hR, g, h, ?_⟩
  intro z hz
  obtain ⟨hgz, hhz, hgoz, hhoz, hwz, haz⟩ := hball hz
  exact ⟨hgz, hhz, hgoz, hhoz, hwz, fun f hf hfo =>
    eventuallyEq_zagierConjugate_basis hf hgz hhz haz hfo hgoz hhoz hwz⟩

end DirichletL
