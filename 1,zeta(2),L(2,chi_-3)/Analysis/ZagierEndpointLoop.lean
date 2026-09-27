import Analysis.ZagierEndpointContinuation

/-!
The endpoint symmetry transfers the actual circle continuation at zero
to a loop at the other endpoint of CDT v2 equation `zagr`. This supplies
the second local continuation calculation needed in Lemma `14functions`.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

theorem analyticContinuationAlong_zagierEndpointTransform
    {T : Type*} [TopologicalSpace T] {γ : T → ℂ} {f : T → ℂ → ℂ}
    (hf : AnalyticContinuationAlong γ f) (hγ : ∀ t, γ t ≠ 1) :
    AnalyticContinuationAlong (fun t => zagierEndpointCoordinate (γ t))
      (fun t => zagierEndpointTransform (f t)) := by
  have hδ : Continuous (fun t => zagierEndpointCoordinate (γ t)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (analyticAt_zagierEndpointCoordinate (hγ t)).continuousAt.comp hf.continuous.continuousAt)
  have hne (t : T) := zagierEndpointCoordinate_ne_one (hγ t)
  have hc := hf.comp hδ (fun t => analyticAt_zagierEndpointCoordinate (hne t))
    (fun t => zagierEndpointCoordinate_self (hγ t))
  have hw : AnalyticContinuationAlong (fun t => zagierEndpointCoordinate (γ t))
      (fun _ z => (1 - z)⁻¹) :=
    AnalyticContinuationAlong.const hδ (fun t =>
      (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr (hne t).symm))
  simpa only [zagierEndpointTransform, div_eq_mul_inv] using hc.mul hw

/-- The image of the small circle under the coordinate exchanging zero and `1/9`. -/
noncomputable def zagierEndpointCirclePath (r : ℝ) (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    Path (zagierEndpointCoordinate (r : ℂ)) (zagierEndpointCoordinate (r : ℂ)) :=
  (complexCirclePath r).map' (f := zagierEndpointCoordinate) (by
    rintro z ⟨t, rfl⟩
    have hne : complexCirclePath r t ≠ 1 :=
      complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t
    exact (analyticAt_zagierEndpointCoordinate hne).continuousAt.continuousWithinAt)

@[simp] theorem zagierEndpointCirclePath_apply (r : ℝ) (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (t : I) : zagierEndpointCirclePath r hr t =
      zagierEndpointCoordinate (complexCirclePath r t) := rfl

theorem zagierEndpointCirclePath_coordinate (r : ℝ) (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (t : I) : zagierEndpointCoordinate (zagierEndpointCirclePath r hr t) =
      complexCirclePath r t :=
  zagierEndpointCoordinate_self
    (complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t)

theorem zagierSecondOrder_circle_regular (r : ℝ) (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (t : I) : complexCirclePath r t * (1 - complexCirclePath r t) *
      (1 - 9 * complexCirclePath r t) ≠ 0 := by
  have hn : ‖complexCirclePath r t‖ = r := by
    rw [norm_complexCirclePath, abs_of_pos hr.1]
  have hz : complexCirclePath r t ≠ 0 := by
    intro he
    rw [he, norm_zero] at hn
    linarith [hr.1]
  have h₁ := complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t
  refine mul_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr h₁.symm)) ?_
  intro he
  have hz₉ : complexCirclePath r t = 1 / 9 := by linear_combination -(1 / 9 : ℂ) * he
  rw [hz₉] at hn
  norm_num at hn
  linarith [hr.2]

theorem zagierSecondOrder_endpointCircle_regular (r : ℝ) (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (t : I) : zagierEndpointCirclePath r hr t * (1 - zagierEndpointCirclePath r hr t) *
      (1 - 9 * zagierEndpointCirclePath r hr t) ≠ 0 := by
  have hreg := zagierSecondOrder_circle_regular r hr t
  have hc := zagierEndpointCirclePath_coordinate r hr t
  have h₁ := zagierEndpointCoordinate_ne_one
    (complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t)
  have hz : zagierEndpointCirclePath r hr t ≠ 0 := by
    intro he
    rw [he, zagierEndpointCoordinate_zero] at hc
    apply hreg
    rw [← hc]
    norm_num
  refine mul_ne_zero (mul_ne_zero hz (sub_ne_zero.mpr h₁.symm)) ?_
  intro he
  have hz₉ : zagierEndpointCirclePath r hr t = 1 / 9 := by
    linear_combination -(1 / 9 : ℂ) * he
  rw [hz₉, one_div, zagierEndpointCoordinate_one_div_nine] at hc
  apply hreg
  rw [← hc]
  simp

theorem analyticContinuationAlong_zagierEndpointSolution_circle (r : ℝ)
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    AnalyticContinuationAlong (zagierEndpointCirclePath r hr)
      (fun _ => zagierEndpointSolution) := by
  apply AnalyticContinuationAlong.const (zagierEndpointCirclePath r hr).continuous
  intro t
  apply analyticAt_zagierEndpointSolution
  · exact zagierEndpointCoordinate_ne_one
      (complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t)
  · rw [zagierEndpointCirclePath_coordinate, norm_complexCirclePath, abs_of_pos hr.1]
    exact hr.2

theorem exists_zagierAnalytic_endpointContinuation_lt {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, ∃ hr : r ∈ Ioo 0 (1 / 9 : ℝ), r < R ∧ ∃ b : ℂ, b ≠ 0 ∧ ∃ f : I → ℂ → ℂ,
      AnalyticContinuationAlong (zagierEndpointCirclePath r hr) f ∧
        (∀ t : I, zagierSecondOrderODE (f t) =ᶠ[𝓝 (zagierEndpointCirclePath r hr t)] 0) ∧
          f 0 =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))] zagierAnalytic ∧
            (f 1 =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))] fun z =>
              zagierAnalytic z + b * (2 * Real.pi * Complex.I) * zagierEndpointSolution z) ∧
                ¬f 0 =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))] f 1 := by
  obtain ⟨r, hr, hrR, b, hb, f, hf, hfo, hf₀, hf₁, _⟩ :=
    exists_zagierEndpointSolution_continuation_lt hR
  have hne (t : I) : complexCirclePath r t ≠ 1 :=
    complexCirclePath_ne_one (by rw [abs_of_pos hr.1]; linarith [hr.2]) t
  have hδne (t : I) : zagierEndpointCirclePath r hr t ≠ 1 :=
    zagierEndpointCoordinate_ne_one (hne t)
  have hc : AnalyticContinuationAlong (zagierEndpointCirclePath r hr)
      (fun t => zagierEndpointTransform (f t)) :=
    analyticContinuationAlong_zagierEndpointTransform hf hne
  let F : I → ℂ → ℂ := fun t z => (8 / 9 : ℂ) * zagierEndpointTransform (f t) z
  have hs : AnalyticContinuationAlong (zagierEndpointCirclePath r hr)
      (fun _ _ => (8 / 9 : ℂ)) :=
    AnalyticContinuationAlong.const (zagierEndpointCirclePath r hr).continuous
      (fun _ => analyticAt_const)
  have hF : AnalyticContinuationAlong (zagierEndpointCirclePath r hr) F := hs.mul hc
  have hFo (t : I) : zagierSecondOrderODE (F t) =ᶠ[𝓝 (zagierEndpointCirclePath r hr t)] 0 := by
    have ha : AnalyticAt ℂ (f t) (zagierEndpointCoordinate (zagierEndpointCirclePath r hr t)) := by
      rw [zagierEndpointCirclePath_coordinate]
      exact hf.analytic t
    have he : zagierSecondOrderODE (f t) =ᶠ[
        𝓝 (zagierEndpointCoordinate (zagierEndpointCirclePath r hr t))] 0 := by
      rw [zagierEndpointCirclePath_coordinate]
      exact hfo t
    filter_upwards [(hc.analytic t).eventually_analyticAt,
      eventually_zagierSecondOrderODE_endpointTransform (hδne t) ha he] with z hz hzo
    rw [show F t = fun w => (8 / 9 : ℂ) * zagierEndpointTransform (f t) w from rfl,
      zagierSecondOrderODE_const_mul hz, hzo, Pi.zero_apply, mul_zero]
  have hrne : (r : ℂ) ≠ 1 := by exact_mod_cast (show r ≠ 1 by linarith [hr.2])
  have hqne : zagierEndpointCoordinate (r : ℂ) ≠ 1 := zagierEndpointCoordinate_ne_one hrne
  have hT₀ : zagierEndpointTransform (f 0) =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))]
      zagierEndpointTransform zagierEndpointSolution :=
    eventuallyEq_zagierEndpointTransform hqne (by
      simpa only [zagierEndpointCoordinate_self hrne] using hf₀)
  have hT₁ : zagierEndpointTransform (f 1) =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))]
      zagierEndpointTransform (fun z => zagierEndpointSolution z +
        b * (2 * Real.pi * Complex.I) * zagierAnalytic z) :=
    eventuallyEq_zagierEndpointTransform hqne (by
      simpa only [zagierEndpointCoordinate_self hrne] using hf₁)
  have hF₀ : F 0 =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))] zagierAnalytic := by
    filter_upwards [hT₀, eventually_ne_nhds hqne] with z hz hzn
    dsimp [F]
    rw [hz, zagierEndpointSolution, zagierEndpointTransform_twice _ hzn]
    ring
  have hF₁ : F 1 =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))] fun z =>
      zagierAnalytic z + ((8 / 9 : ℂ) * b) * (2 * Real.pi * Complex.I) *
        zagierEndpointSolution z := by
    filter_upwards [hT₁, eventually_ne_nhds hqne] with z hz hzn
    dsimp [F]
    rw [hz]
    have he := zagierEndpointTransform_linearCombination zagierEndpointSolution zagierAnalytic
      1 (b * (2 * Real.pi * Complex.I)) z
    simp only [one_mul] at he
    rw [he, zagierEndpointSolution, zagierEndpointTransform_twice _ hzn]
    ring
  have hb' : (8 / 9 : ℂ) * b ≠ 0 := mul_ne_zero (by norm_num) hb
  refine ⟨r, hr, hrR, (8 / 9 : ℂ) * b, hb', F, hF, hFo, hF₀, hF₁, ?_⟩
  intro he
  have h := ((hF₀.symm.trans he).trans hF₁).eq_of_nhds
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hk : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero
  have hS : zagierEndpointSolution (zagierEndpointCoordinate (r : ℂ)) ≠ 0 := by
    intro hz
    have hpos := zagierEndpointSolution_ofReal_re_pos (zagierEndpointCoordinate_mem_Ioo hr)
    rw [← zagierEndpointCoordinate_ofReal, hz] at hpos
    simp at hpos
  exact mul_ne_zero (mul_ne_zero hb' hk) hS (by linear_combination -h)

theorem exists_zagierAnalytic_endpointContinuation :
    ∃ r : ℝ, ∃ hr : r ∈ Ioo 0 (1 / 9 : ℝ), ∃ b : ℂ, b ≠ 0 ∧ ∃ f : I → ℂ → ℂ,
      AnalyticContinuationAlong (zagierEndpointCirclePath r hr) f ∧
        (∀ t : I, zagierSecondOrderODE (f t) =ᶠ[𝓝 (zagierEndpointCirclePath r hr t)] 0) ∧
          f 0 =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))] zagierAnalytic ∧
            (f 1 =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))] fun z =>
              zagierAnalytic z + b * (2 * Real.pi * Complex.I) * zagierEndpointSolution z) ∧
                ¬f 0 =ᶠ[𝓝 (zagierEndpointCoordinate (r : ℂ))] f 1 := by
  obtain ⟨r, hr, _, b, hb, f, hf, hE, h₀, h₁, hne⟩ :=
    exists_zagierAnalytic_endpointContinuation_lt (R := 1) (by norm_num)
  exact ⟨r, hr, b, hb, f, hf, hE, h₀, h₁, hne⟩

end DirichletL
