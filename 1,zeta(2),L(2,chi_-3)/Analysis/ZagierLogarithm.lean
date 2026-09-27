import Analysis.ZagierWronskian

/-!
A normalized logarithmic companion at zero for CDT v2 equation `zagr`.
The exact weighted Wronskian supplies local data for Lemma `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The analytic factor in the reduction-of-order integrand at zero. -/
noncomputable def zagierLogarithmFactor (z : ℂ) : ℂ :=
  1 / ((1 - z) * (1 - 9 * z) * zagierAnalytic z ^ 2)

theorem analyticAt_zagierLogarithmFactor_zero :
    AnalyticAt ℂ zagierLogarithmFactor 0 := by
  have hH : AnalyticAt ℂ zagierAnalytic 0 := analyticAt_zagierAnalytic (by norm_num)
  have hp : AnalyticAt ℂ (fun z : ℂ => (1 - z) * (1 - 9 * z)) 0 := by fun_prop
  exact analyticAt_const.div (hp.mul (hH.pow 2)) (by simp [zagierAnalytic_zero])

@[simp] theorem zagierLogarithmFactor_zero : zagierLogarithmFactor 0 = 1 := by
  simp [zagierLogarithmFactor, zagierAnalytic_zero]

/-- The removable part of the reduction-of-order integrand, including its value at zero. -/
noncomputable def zagierLogarithmIntegrand : ℂ → ℂ := dslope zagierLogarithmFactor 0

theorem analyticAt_zagierLogarithmIntegrand_zero :
    AnalyticAt ℂ zagierLogarithmIntegrand 0 := by
  obtain ⟨p, hp⟩ := analyticAt_zagierLogarithmFactor_zero
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem zagierLogarithmIntegrand_eq {z : ℂ} (hz : z ≠ 0) :
    zagierLogarithmIntegrand z = (zagierLogarithmFactor z - 1) / z := by
  rw [zagierLogarithmIntegrand, dslope_of_ne _ hz]
  simp [slope, div_eq_mul_inv, mul_comm]

/-- The analytic correction to the logarithm, normalized to vanish at zero. -/
noncomputable def zagierLogarithmCorrection : ℂ → ℂ :=
  Classical.choose (exists_analytic_primitive analyticAt_zagierLogarithmIntegrand_zero)

theorem analyticAt_zagierLogarithmCorrection_zero :
    AnalyticAt ℂ zagierLogarithmCorrection 0 :=
  (Classical.choose_spec (exists_analytic_primitive analyticAt_zagierLogarithmIntegrand_zero)).1

@[simp] theorem zagierLogarithmCorrection_zero : zagierLogarithmCorrection 0 = 0 :=
  (Classical.choose_spec (exists_analytic_primitive analyticAt_zagierLogarithmIntegrand_zero)).2.1

theorem eventually_hasDerivAt_zagierLogarithmCorrection :
    ∀ᶠ z in 𝓝 0, HasDerivAt zagierLogarithmCorrection (zagierLogarithmIntegrand z) z :=
  (Classical.choose_spec (exists_analytic_primitive analyticAt_zagierLogarithmIntegrand_zero)).2.2

/-- The local companion using the principal logarithm on the slit plane. -/
noncomputable def zagierLogarithmicSolution (z : ℂ) : ℂ :=
  zagierAnalytic z * (Complex.log z + zagierLogarithmCorrection z)

theorem eventually_zagierLogarithmicProduct :
    ∀ᶠ z in 𝓝 0, ∀ ℓ : ℂ → ℂ, z ≠ 0 → AnalyticAt ℂ ℓ z →
      (∀ᶠ w in 𝓝 z, HasDerivAt ℓ w⁻¹ w) →
        AnalyticAt ℂ (fun w => zagierAnalytic w * (ℓ w + zagierLogarithmCorrection w)) z ∧
          zagierSecondOrderODE (fun w => zagierAnalytic w * (ℓ w + zagierLogarithmCorrection w)) z = 0 ∧
            zagierWeightedWronskian zagierAnalytic
              (fun w => zagierAnalytic w * (ℓ w + zagierLogarithmCorrection w)) z = 1 := by
  have hH : AnalyticAt ℂ zagierAnalytic 0 := analyticAt_zagierAnalytic (by norm_num)
  have hnorm : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 / 9 :=
    continuous_norm.continuousAt.eventually_lt_const (by norm_num)
  have hu : ∀ᶠ z : ℂ in 𝓝 0, (1 - z) * (1 - 9 * z) ≠ 0 :=
    (show ContinuousAt (fun z : ℂ => (1 - z) * (1 - 9 * z)) 0 by fun_prop).eventually_ne
      (by norm_num)
  have hHne : ∀ᶠ z in 𝓝 0, zagierAnalytic z ≠ 0 :=
    hH.continuousAt.eventually_ne (by rw [zagierAnalytic_zero]; norm_num)
  have hlocal : ∀ᶠ z in 𝓝 0, ∀ ℓ : ℂ → ℂ, z ≠ 0 → AnalyticAt ℂ ℓ z → HasDerivAt ℓ z⁻¹ z →
      AnalyticAt ℂ (fun w => zagierAnalytic w * (ℓ w + zagierLogarithmCorrection w)) z ∧
        zagierWeightedWronskian zagierAnalytic
          (fun w => zagierAnalytic w * (ℓ w + zagierLogarithmCorrection w)) z = 1 := by
    filter_upwards [hnorm, hu, hHne,
      analyticAt_zagierLogarithmCorrection_zero.eventually_analyticAt,
      eventually_hasDerivAt_zagierLogarithmCorrection] with z hz huz hHz hB hBd
    intro ℓ hz₀ hℓ hℓd
    have ha := analyticAt_zagierAnalytic hz
    refine ⟨ha.mul (hℓ.add hB), ?_⟩
    have hd : HasDerivAt (fun w => zagierAnalytic w * (ℓ w + zagierLogarithmCorrection w))
        (deriv zagierAnalytic z * (ℓ z + zagierLogarithmCorrection z) +
          zagierAnalytic z * (z⁻¹ + zagierLogarithmIntegrand z)) z :=
      ha.differentiableAt.hasDerivAt.mul (hℓd.add hBd)
    rw [zagierWeightedWronskian, hd.deriv]
    rw [zagierLogarithmIntegrand_eq hz₀]
    dsimp [zagierLogarithmFactor]
    have h₁ := (mul_ne_zero_iff.mp huz).1
    have h₉ := (mul_ne_zero_iff.mp huz).2
    field_simp [hz₀, h₁, h₉, hHz]
    linear_combination mul_inv_cancel₀ h₉
  filter_upwards [hlocal, hlocal.eventually_nhds, hnorm, hHne] with z hz hnear hn hHz
  intro ℓ hz₀ hℓ hℓd
  obtain ⟨ha, hw⟩ := hz ℓ hz₀ hℓ hℓd.self_of_nhds
  refine ⟨ha, ?_, hw⟩
  have he : zagierWeightedWronskian zagierAnalytic
      (fun w => zagierAnalytic w * (ℓ w + zagierLogarithmCorrection w)) =ᶠ[𝓝 z] fun _ => 1 := by
    filter_upwards [hnear, eventually_ne_nhds hz₀, hℓ.eventually_analyticAt, hℓd]
      with w hw hw₀ hwa hwd
    exact (hw ℓ hw₀ hwa hwd).2
  have hd := (hasDerivAt_zagierWeightedWronskian (analyticAt_zagierAnalytic hn) ha).deriv
  rw [he.deriv_eq, deriv_const, show zagierSecondOrderODE zagierAnalytic z = 0 from
    zagierAnalytic_ode hn, mul_zero, sub_zero] at hd
  exact (mul_eq_zero.mp hd.symm).resolve_left hHz

theorem eventually_zagierLogarithmicSolution :
    ∀ᶠ z in 𝓝 0, z ∈ Complex.slitPlane →
      AnalyticAt ℂ zagierLogarithmicSolution z ∧
        zagierSecondOrderODE zagierLogarithmicSolution z = 0 ∧
          zagierWeightedWronskian zagierAnalytic zagierLogarithmicSolution z = 1 := by
  filter_upwards [eventually_zagierLogarithmicProduct] with z hz
  intro hs
  exact hz Complex.log (Complex.slitPlane_ne_zero hs) (analyticAt_clog hs) (by
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds hs] with w hw
    exact Complex.hasDerivAt_log hw)

end DirichletL
