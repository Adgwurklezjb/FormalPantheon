import Analysis.AnalyticPrimitives
import Analysis.ZagierSecondOrderGerms

/-!
The self-adjoint Wronskian identity for CDT v2 equation `zagr` and the
unique analytic solution line at zero, used in Lemma `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The Wronskian multiplied by the leading coefficient of CDT's equation. -/
noncomputable def zagierWeightedWronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * (1 - 9 * z) * (f z * deriv g z - deriv f z * g z)

theorem hasDerivAt_zagierWeightedWronskian {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    HasDerivAt (zagierWeightedWronskian f g)
      (f z * zagierSecondOrderODE g z - g z * zagierSecondOrderODE f z) z := by
  have hp := ((hasDerivAt_id z).mul ((hasDerivAt_id z).const_sub 1)).mul
    (((hasDerivAt_id z).const_mul 9).const_sub 1)
  have hw := (hf.differentiableAt.hasDerivAt.mul hg.deriv.differentiableAt.hasDerivAt).sub
    (hf.deriv.differentiableAt.hasDerivAt.mul hg.differentiableAt.hasDerivAt)
  convert hp.mul hw using 1
  dsimp [zagierSecondOrderODE]
  ring

theorem eventuallyEq_zagierWeightedWronskian_of_ode {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hfode : zagierSecondOrderODE f =ᶠ[𝓝 z] 0)
    (hgode : zagierSecondOrderODE g =ᶠ[𝓝 z] 0) :
    zagierWeightedWronskian f g =ᶠ[𝓝 z] fun _ => zagierWeightedWronskian f g z := by
  apply eventuallyEq_const_of_eventually_hasDerivAt_zero
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, hfode, hgode]
    with w hwf hwg hwof hwog
  simpa only [hwof, hwog, Pi.zero_apply, mul_zero, sub_self] using
    hasDerivAt_zagierWeightedWronskian hwf hwg

theorem eventuallyEq_mul_zagierAnalytic_of_analyticAt_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hode : zagierSecondOrderODE f =ᶠ[𝓝 0] 0) :
    f =ᶠ[𝓝 0] fun z => f 0 * zagierAnalytic z := by
  have hH : AnalyticAt ℂ zagierAnalytic 0 := analyticAt_zagierAnalytic (by norm_num)
  have hnorm : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 / 9 :=
    continuous_norm.continuousAt.eventually_lt_const (by norm_num)
  have hHo : zagierSecondOrderODE zagierAnalytic =ᶠ[𝓝 0] 0 := by
    filter_upwards [hnorm] with z hz
    exact zagierAnalytic_ode hz
  have hW := eventuallyEq_zagierWeightedWronskian_of_ode hH hf hHo hode
  have hu : ∀ᶠ z : ℂ in 𝓝 0, (1 - z) * (1 - 9 * z) ≠ 0 :=
    (show ContinuousAt (fun z : ℂ => (1 - z) * (1 - 9 * z)) 0 by fun_prop).eventually_ne
      (by norm_num)
  have hHne : ∀ᶠ z in 𝓝 0, zagierAnalytic z ≠ 0 :=
    hH.continuousAt.eventually_ne (by rw [zagierAnalytic_zero]; norm_num)
  have hd : ∀ᶠ z in 𝓝 0, HasDerivAt (fun w => f w / zagierAnalytic w) 0 z := by
    filter_upwards [hf.eventually_analyticAt, hnorm, hW, hu, hHne] with z hfz hz hw huz hHz
    have hn : zagierAnalytic z * deriv f z - deriv zagierAnalytic z * f z = 0 := by
      by_cases hz₀ : z = 0
      · subst z
        have hf₀ := hode.eq_of_nhds
        norm_num [zagierSecondOrderODE] at hf₀
        rw [zagierAnalytic_zero, deriv_zagierAnalytic_zero]
        linear_combination hf₀
      · have ha : z * (1 - z) * (1 - 9 * z) ≠ 0 := by
          rw [mul_assoc]
          exact mul_ne_zero hz₀ huz
        simpa only [zagierWeightedWronskian, zero_mul, mul_eq_zero,
          ha, false_or] using hw
    have hq := hfz.differentiableAt.hasDerivAt.div
      (analyticAt_zagierAnalytic hz).differentiableAt.hasDerivAt hHz
    convert hq using 1
    rw [show deriv f z * zagierAnalytic z - f z * deriv zagierAnalytic z = 0 by
      linear_combination hn, zero_div]
  have he := eventuallyEq_const_of_eventually_hasDerivAt_zero hd
  filter_upwards [he, hHne] with z hz hHz
  simpa only [zagierAnalytic_zero, div_one] using (div_eq_iff hHz).mp hz

end DirichletL
