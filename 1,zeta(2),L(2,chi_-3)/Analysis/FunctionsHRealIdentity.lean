import Analysis.FunctionsHRadius
import Analysis.HauptmodulBoundary
import Analysis.HauptmodulProductEvaluation
import Analysis.QSeriesBoundary

/-!
The actual H-product identities on the real q interval in CDT v2,
Section 11.1, Lemma `defabc`. The analytic transport and endpoint checks
-/

namespace DirichletL

open Filter Set
open scoped Topology ENNReal

private theorem eqOn_hauptmodul_interval {f g : ℂ → ℂ}
    (hf : ∀ z, ‖z‖ < 1 / 9 → AnalyticAt ℂ f z)
    (hg : ∀ z, ‖z‖ < 1 → AnalyticAt ℂ g z)
    (he : (fun q => f (hauptmodulProduct q)) =ᶠ[𝓝 0]
      fun q => zagierAnalytic (hauptmodulProduct q) * g q)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    f (hauptmodulProduct (q : ℂ)) = zagierAnalytic (hauptmodulProduct (q : ℂ)) * g (q : ℂ) := by
  let U := Complex.ofReal '' Ico (0 : ℝ) 1
  have hn {z : ℂ} (hz : z ∈ U) : ‖z‖ < 1 := by
    obtain ⟨r, hr, rfl⟩ := hz
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1] using hr.2
  have hx {z : ℂ} (hz : z ∈ U) : ‖hauptmodulProduct z‖ < 1 / 9 := by
    obtain ⟨r, hr, rfl⟩ := hz
    rcases hr.1.eq_or_lt with hr0 | hr0
    · rw [← hr0]
      norm_num [hauptmodulProduct]
    · obtain ⟨x, hx, he⟩ := hauptmodulProduct_ofReal_mem hr0 hr.2
      rw [← he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
      exact hx.2
  have hH {z : ℂ} (hz : z ∈ U) : AnalyticAt ℂ hauptmodulProduct z :=
    differentiableOn_hauptmodulProduct.analyticAt
      (Metric.isOpen_ball.mem_nhds (by simpa using hn hz))
  have hleft : AnalyticOnNhd ℂ (fun z => f (hauptmodulProduct z)) U :=
    fun z hz => (hf _ (hx hz)).comp (hH hz)
  have hright : AnalyticOnNhd ℂ (fun z => zagierAnalytic (hauptmodulProduct z) * g z) U :=
    fun z hz => ((analyticAt_zagierAnalytic (hx hz)).comp (hH hz)).mul (hg z (hn hz))
  have hU : IsPreconnected U :=
    isPreconnected_Ico.image Complex.ofReal Complex.continuous_ofReal.continuousOn
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hU
    (by exact ⟨0, by norm_num, by norm_num⟩) he ⟨q, ⟨hq0, hq1⟩, rfl⟩

private theorem eventuallyEq_hauptmodul_product_identity {f g : ℂ → ℂ}
    (he : f =ᶠ[𝓝 0] fun z => zagierAnalytic z * g (hauptmodulInverseAnalytic z)) :
    (fun q => f (hauptmodulProduct q)) =ᶠ[𝓝 0]
      fun q => zagierAnalytic (hauptmodulProduct q) * g q := by
  have hH : Tendsto hauptmodulProduct (𝓝 0) (𝓝 0) := by
    simpa only [hauptmodulProduct, qEulerProduct_zero, zero_mul, zero_div] using
      hasFPowerSeriesAt_hauptmodulProduct.continuousAt.tendsto
  have hprod : hauptmodulAnalytic =ᶠ[𝓝 0] hauptmodulProduct := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2 ^ 25)]
      with q hq
    exact hauptmodulAnalytic_eq_product (by simpa using hq)
  filter_upwards [he.comp_tendsto hH, hauptmodulInverseAnalytic_left_inverse, hprod]
    with q hq hinv hprodq
  simp only [Function.comp_apply] at hq
  rw [hq]
  have hinv' : hauptmodulInverseAnalytic (hauptmodulProduct q) = q := by
    simpa only [Function.comp_apply, hprodq, id_eq] using hinv
  rw [hinv']

theorem hBAnalytic_hauptmodulProduct {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    hBAnalytic (hauptmodulProduct (q : ℂ)) =
      zagierAnalytic (hauptmodulProduct (q : ℂ)) * betaAnalytic (q : ℂ) := by
  apply eqOn_hauptmodul_interval
    (fun z hz => hasFPowerSeriesOnBall_hBAnalytic.analyticAt_of_mem (by
      rw [show (1 / 9 : ℝ≥0∞) = ENNReal.ofReal (1 / 9 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat],
        Metric.emetric_ball]
      simpa using hz))
    (fun z hz => hasFPowerSeriesOnBall_betaAnalytic.analyticAt_of_mem ?_)
    (eventuallyEq_hauptmodul_product_identity hBAnalytic_eq_product) hq0 hq1
  rw [← ENNReal.ofReal_one, Metric.emetric_ball]
  simpa using hz

theorem hCAnalytic_hauptmodulProduct {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    hCAnalytic (hauptmodulProduct (q : ℂ)) =
      zagierAnalytic (hauptmodulProduct (q : ℂ)) * gammaAnalytic (q : ℂ) := by
  apply eqOn_hauptmodul_interval
    (fun z hz => hasFPowerSeriesOnBall_hCAnalytic.analyticAt_of_mem (by
      rw [show (1 / 9 : ℝ≥0∞) = ENNReal.ofReal (1 / 9 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
          ENNReal.ofReal_ofNat],
        Metric.emetric_ball]
      simpa using hz))
    (fun z hz => hasFPowerSeriesOnBall_gammaAnalytic.analyticAt_of_mem ?_)
    (eventuallyEq_hauptmodul_product_identity hCAnalytic_eq_product) hq0 hq1
  rw [← ENNReal.ofReal_one, Metric.emetric_ball]
  simpa using hz

end DirichletL
