import Analysis.ZagierAnalytic

/-!
The singularity of the actual `H_A` at `1/9` in CDT v2, Lemma `defabc`.
The self-adjoint form of equation `zagr` gives a logarithmic lower bound
on the real interval and excludes continuous extension at its right endpoint.
-/

namespace DirichletL

open Filter Set
open scoped Topology

/-- The real restriction of the actual normalized Zagier solution. -/
noncomputable def zagierReal (x : ℝ) : ℝ := (zagierAnalytic x).re

theorem hasSum_zagierReal {x : ℝ} (hx : |x| < 1 / 9) :
    HasSum (fun n : ℕ => (zagierC n : ℝ) * x ^ n) (zagierReal x) := by
  simpa [zagierReal, Complex.mul_re, ← Complex.ofReal_pow] using
    Complex.hasSum_re (hasSum_zagierAnalytic (z := x) (by simpa using hx))

theorem one_le_zagierReal {x : ℝ} (hx₀ : 0 ≤ x) (hx : x < 1 / 9) :
    1 ≤ zagierReal x := by
  have hs := hasSum_zagierReal (by rwa [abs_of_nonneg hx₀])
  have h := hs.summable.le_tsum 0 (fun _ _ => by positivity)
  simpa [hs.tsum_eq, zagierC_zero] using h

theorem hasDerivAt_zagierReal {x : ℝ} (hx : |x| < 1 / 9) :
    HasDerivAt zagierReal (deriv zagierAnalytic x).re x := by
  have h := (analyticAt_zagierAnalytic (z := x) (by simpa using hx)).differentiableAt
  exact h.hasDerivAt.real_of_complex

/-- The self-adjoint flux for CDT equation `zagr` on the real axis. -/
noncomputable def zagierRealFlux (x : ℝ) : ℝ :=
  x * (1 - x) * (1 - 9 * x) * (deriv zagierAnalytic x).re

theorem zagierRealFlux_eq {x : ℝ} (hx : |x| < 1 / 9) :
    zagierRealFlux x = x * (1 - x) * (1 - 9 * x) * deriv zagierReal x := by
  rw [(hasDerivAt_zagierReal hx).deriv]
  rfl

theorem hasDerivAt_zagierRealFlux {x : ℝ} (hx : |x| < 1 / 9) :
    HasDerivAt zagierRealFlux ((3 - 9 * x) * zagierReal x) x := by
  have ha := analyticAt_zagierAnalytic (z := x) (by simpa using hx)
  have hd := ha.deriv.differentiableAt.hasDerivAt.real_of_complex
  have hp := ((hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub 1)).mul
    (((hasDerivAt_id x).const_mul 9).const_sub 1)
  have h := hp.mul hd
  have he := congrArg Complex.re (zagierAnalytic_ode (z := x) (by simpa using hx))
  norm_num [Complex.mul_re, Complex.mul_im, pow_two] at he
  convert h using 1
  dsimp [zagierRealFlux, zagierReal]
  linear_combination -he

theorem two_mul_le_zagierRealFlux {x : ℝ} (hx₀ : 0 ≤ x) (hx : x < 1 / 9) :
    2 * x ≤ zagierRealFlux x := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 x) :=
    hasDerivAt_zagierRealFlux (x := t) (by rw [abs_of_nonneg ht.1]; linarith [ht.2])
  have h := (convex_Icc (0 : ℝ) x).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (C := 2) (fun t ht => ?_) 0 (by simp [hx₀]) x (by simp [hx₀]) hx₀
  · simpa [zagierRealFlux] using h
  · have ht' := interior_subset ht
    rw [(hd t ht').deriv]
    have hu := one_le_zagierReal ht'.1 (lt_of_le_of_lt ht'.2 hx)
    have ht₉ : 2 ≤ 3 - 9 * t := by linarith [ht'.2]
    nlinarith

theorem two_div_le_deriv_zagierReal {x : ℝ} (hx₀ : 0 < x) (hx : x < 1 / 9) :
    2 / (1 - 9 * x) ≤ deriv zagierReal x := by
  have h := two_mul_le_zagierRealFlux hx₀.le hx
  rw [zagierRealFlux_eq (by rwa [abs_of_pos hx₀])] at h
  have h₁ : 0 < 1 - x := by linarith
  have h₉ : 0 < 1 - 9 * x := by linarith
  have h' : 2 ≤ (1 - x) * (1 - 9 * x) * deriv zagierReal x := by
    nlinarith
  have hd : 0 ≤ deriv zagierReal x := by
    have hp : 0 < (1 - x) * (1 - 9 * x) := mul_pos h₁ h₉
    nlinarith
  rw [div_le_iff₀ h₉]
  have hp : 0 ≤ x * ((1 - 9 * x) * deriv zagierReal x) := by positivity
  nlinarith

theorem log_lowerBound_zagierReal {x : ℝ} (hx₀ : 0 ≤ x) (hx : x < 1 / 9) :
    1 - (2 / 9) * Real.log (1 - 9 * x) ≤ zagierReal x := by
  let f : ℝ → ℝ := fun t => zagierReal t + (2 / 9) * Real.log (1 - 9 * t)
  have hd (t : ℝ) (ht : t ∈ Icc 0 x) :
      HasDerivAt f (deriv zagierReal t - 2 / (1 - 9 * t)) t := by
    have ht₉ : 0 < 1 - 9 * t := by linarith [ht.2]
    have hu := hasDerivAt_zagierReal (x := t)
      (by rw [abs_of_nonneg ht.1]; linarith [ht.2])
    have hl := ((((hasDerivAt_id t).const_mul 9).const_sub 1).log ht₉.ne').const_mul
      (2 / 9)
    convert hu.add hl using 1
    rw [hu.deriv]
    dsimp
    ring
  have hm : MonotoneOn f (Icc 0 x) := monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (by
      intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      rw [interior_Icc] at ht
      exact sub_nonneg.mpr (two_div_le_deriv_zagierReal ht.1 (lt_trans ht.2 hx)))
  have h := hm (by simp [hx₀]) (by simp [hx₀]) hx₀
  simp [f, zagierReal, zagierAnalytic_zero] at h
  change 1 ≤ zagierReal x + (2 / 9) * Real.log (1 - 9 * x) at h
  linarith

theorem tendsto_zagierReal_nhdsLT :
    Tendsto zagierReal (𝓝[<] (1 / 9 : ℝ)) atTop := by
  have ht : Tendsto (fun x : ℝ => 1 - 9 * x) (𝓝[<] (1 / 9 : ℝ)) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : Continuous (fun x : ℝ => 1 - 9 * x) := by fun_prop
      simpa using h.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (1 / 9 : ℝ)) (s := Iio (1 / 9)))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x < (1 / 9 : ℝ) at hx
      change 0 < 1 - 9 * x
      linarith
  have hl := (Real.tendsto_log_nhdsGT_zero.comp ht).const_mul_atBot_of_neg
    (by norm_num : (- (2 / 9) : ℝ) < 0)
  have hb : Tendsto (fun x : ℝ => 1 - (2 / 9) * Real.log (1 - 9 * x))
      (𝓝[<] (1 / 9 : ℝ)) atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_left _ 1 hl
  refine tendsto_atTop_mono' _ ?_ hb
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ x in 𝓝[<] (1 / 9 : ℝ), 0 < x from
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1 / 9)).filter_mono
        nhdsWithin_le_nhds)] with x hx hx₀
  exact log_lowerBound_zagierReal hx₀.le hx

theorem not_continuousAt_of_eventuallyEq_zagierReal {f : ℝ → ℝ}
    (h : f =ᶠ[𝓝[<] (1 / 9 : ℝ)] zagierReal) : ¬ContinuousAt f (1 / 9 : ℝ) := by
  intro hf
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_zagierReal_nhdsLT.congr' h.symm)
    _ (hf.tendsto.mono_left nhdsWithin_le_nhds)

theorem not_continuousAt_of_eventuallyEq_zagierAnalytic {f : ℂ → ℂ}
    (h : (fun x : ℝ => f x) =ᶠ[𝓝[<] (1 / 9 : ℝ)] fun x => zagierAnalytic x) :
    ¬ContinuousAt f (1 / 9 : ℂ) := by
  intro hf
  apply not_continuousAt_of_eventuallyEq_zagierReal (h.fun_comp Complex.re)
  have hf' : ContinuousAt f ((1 / 9 : ℝ) : ℂ) := by simpa using hf
  exact Complex.continuous_re.continuousAt.comp
    (hf'.comp Complex.continuous_ofReal.continuousAt)

theorem not_analyticAt_of_eventuallyEq_zagierAnalytic {f : ℂ → ℂ}
    (h : (fun x : ℝ => f x) =ᶠ[𝓝[<] (1 / 9 : ℝ)] fun x => zagierAnalytic x) :
    ¬AnalyticAt ℂ f (1 / 9 : ℂ) :=
  fun hf => not_continuousAt_of_eventuallyEq_zagierAnalytic h hf.continuousAt

end DirichletL
