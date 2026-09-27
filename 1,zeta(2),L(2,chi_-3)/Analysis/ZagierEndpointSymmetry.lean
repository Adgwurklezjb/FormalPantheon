import Analysis.ZagierRealSingularity

/-!
The endpoint symmetry of the second-order equation `zagr` in CDT v2.
It produces a solution regular at `1/9`, independent of the actual `H_A`
germ on the intervening real interval. This is a local prerequisite for
the irreducibility assertion in the proof of Lemma `14functions`.
-/

namespace DirichletL

open Filter Set
open scoped Topology

/-- The rational coordinate exchanging the two adjacent Zagier singularities. -/
noncomputable def zagierEndpointCoordinate (z : ℂ) : ℂ := (1 - 9 * z) / (9 * (1 - z))

@[simp] theorem zagierEndpointCoordinate_zero : zagierEndpointCoordinate 0 = 1 / 9 := by
  norm_num [zagierEndpointCoordinate]

@[simp] theorem zagierEndpointCoordinate_one_div_nine :
    zagierEndpointCoordinate (9 : ℂ)⁻¹ = 0 := by
  norm_num [zagierEndpointCoordinate]

theorem zagierEndpointCoordinate_ofReal (x : ℝ) :
    zagierEndpointCoordinate x = (((1 - 9 * x) / (9 * (1 - x)) : ℝ) : ℂ) := by
  simp [zagierEndpointCoordinate]

theorem zagierEndpointCoordinate_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 (1 / 9 : ℝ)) :
    (1 - 9 * x) / (9 * (1 - x)) ∈ Ioo 0 (1 / 9 : ℝ) := by
  have hd : 0 < 9 * (1 - x) := by linarith [hx.2]
  constructor
  · exact div_pos (by linarith [hx.2]) hd
  · rw [div_lt_iff₀ hd]
    linarith [hx.1]

theorem one_sub_zagierEndpointCoordinate {z : ℂ} (hz : z ≠ 1) :
    1 - zagierEndpointCoordinate z = 8 / (9 * (1 - z)) := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  dsimp [zagierEndpointCoordinate]
  field_simp [hd]
  ring

theorem zagierEndpointCoordinate_ne_one {z : ℂ} (hz : z ≠ 1) :
    zagierEndpointCoordinate z ≠ 1 := by
  have h := div_ne_zero (by norm_num : (8 : ℂ) ≠ 0)
    (mul_ne_zero (by norm_num : (9 : ℂ) ≠ 0) (sub_ne_zero.mpr hz.symm))
  rw [← one_sub_zagierEndpointCoordinate hz] at h
  exact fun he => h (by rw [he, sub_self])

theorem zagierEndpointCoordinate_self {z : ℂ} (hz : z ≠ 1) :
    zagierEndpointCoordinate (zagierEndpointCoordinate z) = z := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  rw [zagierEndpointCoordinate, one_sub_zagierEndpointCoordinate hz]
  dsimp [zagierEndpointCoordinate]
  field_simp [hd]
  ring

theorem analyticAt_zagierEndpointCoordinate {z : ℂ} (hz : z ≠ 1) :
    AnalyticAt ℂ zagierEndpointCoordinate z := by
  have hd : 9 * (1 - z) ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr hz.symm)
  exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div
    (analyticAt_const.mul (analyticAt_const.sub analyticAt_id)) hd

theorem hasDerivAt_zagierEndpointCoordinate {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt zagierEndpointCoordinate (-8 / (9 * (1 - z) ^ 2)) z := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have h := (((hasDerivAt_id z).const_mul 9).const_sub 1).div
    (((hasDerivAt_id z).const_sub 1).const_mul 9) (mul_ne_zero (by norm_num) hd)
  convert h using 1
  dsimp
  field_simp [hd]
  ring

/-- The weight factor accompanying the endpoint coordinate symmetry. -/
noncomputable def zagierEndpointTransform (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f (zagierEndpointCoordinate z) / (1 - z)

theorem zagierEndpointTransform_twice (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 1) :
    zagierEndpointTransform (zagierEndpointTransform f) z = (9 / 8) * f z := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  simp only [zagierEndpointTransform, zagierEndpointCoordinate_self hz,
    one_sub_zagierEndpointCoordinate hz]
  field_simp [hd]

theorem eventuallyEq_zagierEndpointTransform {f g : ℂ → ℂ} {z : ℂ} (hz : z ≠ 1)
    (he : f =ᶠ[𝓝 (zagierEndpointCoordinate z)] g) :
    zagierEndpointTransform f =ᶠ[𝓝 z] zagierEndpointTransform g := by
  filter_upwards [he.comp_tendsto (analyticAt_zagierEndpointCoordinate hz).continuousAt.tendsto]
    with w hw
  exact congrArg (fun v => v / (1 - w)) hw

theorem zagierEndpointTransform_linearCombination (f g : ℂ → ℂ) (a b z : ℂ) :
    zagierEndpointTransform (fun w => a * f w + b * g w) z =
      a * zagierEndpointTransform f z + b * zagierEndpointTransform g z := by
  simp only [zagierEndpointTransform, div_eq_mul_inv]
  ring

theorem analyticAt_zagierEndpointTransform {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 1)
    (hf : AnalyticAt ℂ f (zagierEndpointCoordinate z)) :
    AnalyticAt ℂ (zagierEndpointTransform f) z :=
  (hf.comp (analyticAt_zagierEndpointCoordinate hz)).div
    (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr hz.symm)

theorem hasDerivAt_zagierEndpointTransform {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 1)
    (hf : DifferentiableAt ℂ f (zagierEndpointCoordinate z)) :
    HasDerivAt (zagierEndpointTransform f)
      (f (zagierEndpointCoordinate z) / (1 - z) ^ 2 -
        (8 / 9) * deriv f (zagierEndpointCoordinate z) / (1 - z) ^ 3) z := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have h := (hf.hasDerivAt.comp z (hasDerivAt_zagierEndpointCoordinate hz)).div
    ((hasDerivAt_id z).const_sub 1) hd
  convert h using 1
  dsimp
  field_simp [hd]
  ring

theorem hasDerivAt_deriv_zagierEndpointTransform {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 1)
    (hf : AnalyticAt ℂ f (zagierEndpointCoordinate z)) :
    HasDerivAt (deriv (zagierEndpointTransform f))
      (2 * f (zagierEndpointCoordinate z) / (1 - z) ^ 3 -
        (32 / 9) * deriv f (zagierEndpointCoordinate z) / (1 - z) ^ 4 +
        (64 / 81) * deriv (deriv f) (zagierEndpointCoordinate z) / (1 - z) ^ 5) z := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  have ht := hasDerivAt_zagierEndpointCoordinate hz
  have h0 := hf.differentiableAt.hasDerivAt.comp z ht
  have h1 := hf.deriv.differentiableAt.hasDerivAt.comp z ht
  have h := (h0.div (((hasDerivAt_id z).const_sub 1).pow 2) (pow_ne_zero 2 hd)).sub
    ((h1.const_mul (8 / 9)).div (((hasDerivAt_id z).const_sub 1).pow 3)
      (pow_ne_zero 3 hd))
  have he : deriv (zagierEndpointTransform f) =ᶠ[𝓝 z] fun w =>
      f (zagierEndpointCoordinate w) / (1 - w) ^ 2 -
        (8 / 9) * deriv f (zagierEndpointCoordinate w) / (1 - w) ^ 3 := by
    filter_upwards [eventually_ne_nhds hz,
      (analyticAt_zagierEndpointCoordinate hz).continuousAt.tendsto.eventually
        hf.eventually_analyticAt] with w hw hwf
    exact (hasDerivAt_zagierEndpointTransform hw hwf.differentiableAt).deriv
  convert h.congr_of_eventuallyEq he using 1
  dsimp
  field_simp (discharger := simp [hd]) [hd]
  ring

/-- The polynomial analytic residual of CDT's original second-order equation. -/
noncomputable def zagierSecondOrderODE (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * (1 - 9 * z) * deriv (deriv f) z +
    (1 - 20 * z + 27 * z ^ 2) * deriv f z + (9 * z - 3) * f z

theorem zagierSecondOrderODE_endpointTransform {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 1)
    (hf : AnalyticAt ℂ f (zagierEndpointCoordinate z)) :
    zagierSecondOrderODE (zagierEndpointTransform f) z =
      zagierSecondOrderODE f (zagierEndpointCoordinate z) / (1 - z) := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  rw [zagierSecondOrderODE, (hasDerivAt_deriv_zagierEndpointTransform hz hf).deriv,
    (hasDerivAt_zagierEndpointTransform hz hf.differentiableAt).deriv]
  dsimp [zagierSecondOrderODE, zagierEndpointTransform]
  generalize f (zagierEndpointCoordinate z) = f₀
  generalize deriv f (zagierEndpointCoordinate z) = f₁
  generalize deriv (deriv f) (zagierEndpointCoordinate z) = f₂
  dsimp [zagierEndpointCoordinate]
  field_simp (discharger := simp [hd]) [hd]
  ring

theorem eventually_zagierSecondOrderODE_endpointTransform {f : ℂ → ℂ} {z : ℂ}
    (hz : z ≠ 1) (hf : AnalyticAt ℂ f (zagierEndpointCoordinate z))
    (he : zagierSecondOrderODE f =ᶠ[𝓝 (zagierEndpointCoordinate z)] 0) :
    zagierSecondOrderODE (zagierEndpointTransform f) =ᶠ[𝓝 z] 0 := by
  have ht := (analyticAt_zagierEndpointCoordinate hz).continuousAt.tendsto
  filter_upwards [eventually_ne_nhds hz, ht.eventually hf.eventually_analyticAt,
    he.comp_tendsto ht] with w hw hwf hwe
  dsimp only [Function.comp_apply, Pi.zero_apply] at hwe
  rw [zagierSecondOrderODE_endpointTransform hw hwf, hwe, Pi.zero_apply, zero_div]

/-- The actual solution normalized by the endpoint symmetry. -/
noncomputable def zagierEndpointSolution : ℂ → ℂ := zagierEndpointTransform zagierAnalytic

theorem analyticAt_zagierEndpointSolution {z : ℂ} (hz : z ≠ 1)
    (ht : ‖zagierEndpointCoordinate z‖ < 1 / 9) :
    AnalyticAt ℂ zagierEndpointSolution z :=
  analyticAt_zagierEndpointTransform hz (analyticAt_zagierAnalytic ht)

theorem analyticAt_zagierEndpointSolution_one_div_nine :
  AnalyticAt ℂ zagierEndpointSolution (1 / 9) :=
  analyticAt_zagierEndpointSolution (by norm_num) (by simp)

@[simp] theorem zagierEndpointSolution_one_div_nine :
    zagierEndpointSolution (9 : ℂ)⁻¹ = 9 / 8 := by
  change zagierAnalytic (zagierEndpointCoordinate (9 : ℂ)⁻¹) / (1 - (9 : ℂ)⁻¹) = _
  rw [zagierEndpointCoordinate_one_div_nine, zagierAnalytic_zero]
  norm_num

theorem zagierEndpointSolution_ode {z : ℂ} (hz : z ≠ 1)
    (ht : ‖zagierEndpointCoordinate z‖ < 1 / 9) :
    zagierSecondOrderODE zagierEndpointSolution z = 0 := by
  rw [zagierEndpointSolution,
    zagierSecondOrderODE_endpointTransform hz (analyticAt_zagierAnalytic ht)]
  rw [show zagierSecondOrderODE zagierAnalytic (zagierEndpointCoordinate z) = 0 from
    zagierAnalytic_ode ht, zero_div]

theorem zagierEndpointSolution_ofReal_re_pos {x : ℝ} (hx : x ∈ Ioo 0 (1 / 9 : ℝ)) :
    0 < (zagierEndpointSolution x).re := by
  have ht := zagierEndpointCoordinate_mem_Ioo hx
  have hu := one_le_zagierReal ht.1.le ht.2
  have he : (zagierEndpointSolution x).re =
      zagierReal ((1 - 9 * x) / (9 * (1 - x))) / (1 - x) := by
    change (zagierAnalytic (zagierEndpointCoordinate x) / (1 - (x : ℂ))).re = _
    rw [zagierEndpointCoordinate_ofReal, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.div_ofReal_re]
    rfl
  rw [he]
  exact div_pos (by linarith) (by linarith [hx.2])

theorem not_eventuallyEq_zagierAnalytic_endpointSolution {x : ℝ}
    (hx : x ∈ Ioo 0 (1 / 9 : ℝ)) (c : ℂ) :
    ¬zagierAnalytic =ᶠ[𝓝 (x : ℂ)] fun z => c * zagierEndpointSolution z := by
  intro h
  let U : Set ℂ := Complex.ofReal '' Ioo (0 : ℝ) (1 / 9)
  have hU : IsPreconnected U := isPreconnected_Ioo.image _
    Complex.continuous_ofReal.continuousOn
  have ha : AnalyticOnNhd ℂ zagierAnalytic U := by
    rintro _ ⟨t, ht, rfl⟩
    apply analyticAt_zagierAnalytic
    simpa [abs_of_pos ht.1] using ht.2
  have hb : AnalyticOnNhd ℂ (fun z => c * zagierEndpointSolution z) U := by
    rintro _ ⟨t, ht, rfl⟩
    apply analyticAt_const.mul
    apply analyticAt_zagierEndpointSolution
    · exact_mod_cast (by linarith [ht.2] : t ≠ 1)
    · rw [zagierEndpointCoordinate_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (zagierEndpointCoordinate_mem_Ioo ht).1]
      exact (zagierEndpointCoordinate_mem_Ioo ht).2
  have he := ha.eqOn_of_preconnected_of_eventuallyEq hb hU ⟨x, hx, rfl⟩ h
  apply not_continuousAt_of_eventuallyEq_zagierAnalytic (f := fun z => c * zagierEndpointSolution z)
    (show (fun t : ℝ => c * zagierEndpointSolution t) =ᶠ[𝓝[<] (1 / 9 : ℝ)]
      fun t => zagierAnalytic t from ?_)
    (continuousAt_const.mul analyticAt_zagierEndpointSolution_one_div_nine.continuousAt)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 9)).filter_mono
      nhdsWithin_le_nhds] with t ht ht₀
  exact (he ⟨t, ⟨ht₀, ht⟩, rfl⟩).symm

theorem eq_zero_of_zagierEndpointSolution_relation {x : ℝ}
    (hx : x ∈ Ioo 0 (1 / 9 : ℝ)) {a b : ℂ}
    (h : (fun z => a * zagierAnalytic z + b * zagierEndpointSolution z) =ᶠ[𝓝 (x : ℂ)] 0) :
    a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra ha
    apply not_eventuallyEq_zagierAnalytic_endpointSolution hx (-b / a)
    filter_upwards [h] with z hz
    dsimp at hz ⊢
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff ha).mpr
    linear_combination hz
  refine ⟨ha, ?_⟩
  have h₀ := h.self_of_nhds
  simp only [ha, zero_mul, zero_add, Pi.zero_apply] at h₀
  apply (mul_eq_zero.mp h₀).resolve_right
  intro hz
  have hp := zagierEndpointSolution_ofReal_re_pos hx
  simp [hz] at hp

end DirichletL
