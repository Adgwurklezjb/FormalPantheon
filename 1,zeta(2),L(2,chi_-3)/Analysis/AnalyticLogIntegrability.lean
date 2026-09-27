import Mathlib

/-!
Local logarithmic integrability for CDT v2, supplied TeX 3505-3540 and 4150-4153.
Meanings and zero-germ checks precede these bodies in
-/

open Filter MeasureTheory Set
open scoped Topology

namespace DirichletL

theorem integrableAtFilter_congr_off_point {f g : ℝ → ℝ} {x : ℝ}
    (hf : IntegrableAtFilter f (𝓝 x) volume)
    (hfg : ∀ᶠ t in 𝓝 x, t ≠ x → f t = g t) :
    IntegrableAtFilter g (𝓝 x) volume := by
  obtain ⟨S, hS, hfS⟩ := hf
  obtain ⟨U, hU, hopen, hx⟩ := mem_nhds_iff.mp (inter_mem hS hfg)
  refine ⟨U, hopen.mem_nhds hx, ?_⟩
  apply (hfS.mono_set (fun t ht => (hU ht).1)).congr_fun_ae
  change ∀ᵐ t ∂volume.restrict U, f t = g t
  rw [ae_restrict_iff' hopen.measurableSet]
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ x := by
    simpa only [mem_singleton_iff] using (countable_singleton x).ae_not_mem volume
  filter_upwards [hne] with t ht
  intro htU
  exact (hU htU).2 ht

theorem integrableAtFilter_log_norm_of_analyticAt {f : ℝ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) :
    IntegrableAtFilter (fun t => Real.log ‖f t‖) (𝓝 x) volume := by
  by_cases hz : ∀ᶠ t in 𝓝 x, f t = 0
  · apply integrableAtFilter_congr_off_point
      ((continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).integrableAt_nhds x)
    filter_upwards [hz] with t ht
    intro _
    simp [ht]
  obtain ⟨n, g, hg, hgx, hfactor⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
  have hgood : ∀ᶠ t in 𝓝 x, AnalyticAt ℝ g t ∧ g t ≠ 0 :=
    hg.eventually_analyticAt.and (hg.continuousAt.eventually_ne hgx)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hga : AnalyticOnNhd ℝ g (Metric.ball x δ) := fun t ht => (hball ht).1
  have hcont : ContinuousOn (fun t => Real.log ‖g t‖) (Metric.ball x δ) :=
    hga.continuousOn.norm.log (fun t ht => norm_ne_zero_iff.mpr (hball ht).2)
  have hgint : IntegrableAtFilter (fun t => Real.log ‖g t‖) (𝓝 x) volume := by
    have h := hcont.integrableAt_nhdsWithin (μ := volume) measurableSet_ball
      (Metric.mem_ball_self hδ)
    rwa [nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds x hδ)] at h
  have hlog : IntervalIntegrable (fun t : ℝ => Real.log (t - x)) volume
      (x - 1) (x + 1) := by
    convert (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).comp_sub_right x
      using 1 <;> ring
  have hlogint : IntegrableAtFilter (fun t : ℝ => Real.log (t - x)) (𝓝 x) volume :=
    ⟨Ioc (x - 1) (x + 1), Ioc_mem_nhds (by linarith) (by linarith), hlog.1⟩
  have hmodel : IntegrableAtFilter
      (fun t => (n : ℝ) * Real.log (t - x) + Real.log ‖g t‖) (𝓝 x) volume := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      (hlogint.smul (n : ℝ)).add hgint
  apply integrableAtFilter_congr_off_point hmodel
  filter_upwards [hfactor, hg.continuousAt.eventually_ne hgx] with t ht hgt
  intro htx
  symm
  rw [ht, norm_smul, norm_pow,
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr htx)))
      (norm_ne_zero_iff.mpr hgt),
    Real.log_pow, Real.norm_eq_abs, Real.log_abs]

theorem intervalIntegrable_log_norm_of_analyticOnNhd {f : ℝ → ℂ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (uIcc a b)) :
    IntervalIntegrable (fun t => Real.log ‖f t‖) volume a b := by
  apply (intervalIntegrable_iff' (by finiteness)).mpr
  have hlocal : LocallyIntegrableOn (fun t => Real.log ‖f t‖) (uIcc a b) volume := by
    intro x hx
    exact (integrableAtFilter_log_norm_of_analyticAt (hf x hx)).filter_mono nhdsWithin_le_nhds
  exact hlocal.integrableOn_isCompact isCompact_uIcc

end DirichletL
