import Analysis.TauberianSchwartz

/-!
Smoothed arithmetic sums on the Wiener-Ikehara route to CDT v2 Section 2.2
(supplied TeX 3291-3310). Based on the PrimeNumberTheoremAnd contributors,
Wiener.lean at revision 0766218b21b11ddf24103352ece7f0cb730945e0,
lines 1640-1835, archived with its Apache 2.0 license in
uses Mathlib's canonical Jacobian formula.
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology FourierTransform SchwartzMap ContDiff

theorem hasCompactSupport_comp_exp_of_tsupport_subset {Ψ : ℝ → ℂ}
    (hs : HasCompactSupport Ψ) (hp : tsupport Ψ ⊆ Ioi 0) :
    HasCompactSupport (Ψ ∘ Real.exp) := by
  have hzero : Ψ =ᶠ[𝓝 (0 : ℝ)] 0 :=
    not_mem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl (0 : ℝ) (hp h))
  have htop : ∀ᶠ y : ℝ in atTop, Ψ y = 0 := by
    rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
      cocompact_eq_atBot_atTop] at hs
    exact hs.2
  rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨Real.tendsto_exp_atBot hzero, Real.tendsto_exp_atTop htop⟩

theorem integral_exp_mul_comp_exp (Ψ : ℝ → ℂ) :
    (∫ u : ℝ, (Real.exp u : ℂ) * Ψ (Real.exp u)) = ∫ y in Ioi (0 : ℝ), Ψ y := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := (univ : Set ℝ))
    (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn Ψ
  simpa only [image_univ, Real.range_exp, Measure.restrict_univ,
    abs_of_pos (Real.exp_pos _), Complex.real_smul] using h.symm

theorem exists_schwartz_fourier_exp {Ψ : ℝ → ℂ} (hsm : ContDiff ℝ ∞ Ψ)
    (hs : HasCompactSupport Ψ) (hp : tsupport Ψ ⊆ Ioi 0) :
    ∃ ψ : 𝓢(ℝ, ℂ), ∀ t : ℝ,
      𝓕 ψ t = (Real.exp (2 * Real.pi * t) : ℂ) * Ψ (Real.exp (2 * Real.pi * t)) := by
  have hcont : ContDiff ℝ ∞ (fun t : ℝ => Real.exp (2 * Real.pi * t)) := by fun_prop
  have h₁ : ContDiff ℝ ∞ (fun t : ℝ =>
      (Real.exp (2 * Real.pi * t) : ℂ) * Ψ (Real.exp (2 * Real.pi * t))) :=
    (Complex.ofRealCLM.contDiff.comp hcont).mul (hsm.comp hcont)
  have h₂ : HasCompactSupport (fun t : ℝ =>
      (Real.exp (2 * Real.pi * t) : ℂ) * Ψ (Real.exp (2 * Real.pi * t))) := by
    have hc := (hasCompactSupport_comp_exp_of_tsupport_subset hs hp).comp_homeomorph
      (Homeomorph.mulLeft₀ (2 * Real.pi) Real.two_pi_pos.ne')
    simpa only [Function.comp_def, Homeomorph.coe_mulLeft₀] using
      hc.mul_left (f := fun t : ℝ => (Real.exp (2 * Real.pi * t) : ℂ))
  let h : 𝓢(ℝ, ℂ) := schwartzMapOfHasCompactSupport _ h₁ h₂
  refine ⟨(SchwartzMap.fourierTransformCLE ℂ).symm h, ?_⟩
  intro t
  change SchwartzMap.fourierTransformCLE ℂ ((SchwartzMap.fourierTransformCLE ℂ).symm h) t = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem tendsto_tsum_mul_smoothed {f : ℕ → ℂ} {C : ℝ} {A : ℂ} {G : ℂ → ℂ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : EqOn G (fun s => LSeries f s - A / (s - 1)) {s | 1 < s.re})
    {Ψ : ℝ → ℂ} (hsm : ContDiff ℝ ∞ Ψ) (hs : HasCompactSupport Ψ)
    (hp : tsupport Ψ ⊆ Ioi 0) :
    Tendsto (fun x : ℝ => (∑' n : ℕ, f n * Ψ ((n : ℝ) / x)) / (x : ℂ)) atTop
      (𝓝 (A * ∫ y in Ioi (0 : ℝ), Ψ y)) := by
  obtain ⟨ψ, hψ⟩ := exists_schwartz_fourier_exp hsm hs hp
  have hzero : Ψ 0 = 0 :=
    image_eq_zero_of_nmem_tsupport (fun h => lt_irrefl (0 : ℝ) (hp h))
  have hsamp {x : ℝ} (hx : 0 < x) (n : ℕ) :
      tauberianFourierTerm f ψ x n = f n * Ψ ((n : ℝ) / x) / (x : ℂ) := by
    by_cases hn : n = 0
    · simp [hn, tauberianFourierTerm_zero, hzero]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    unfold tauberianFourierTerm
    rw [hψ]
    have he : 2 * Real.pi * (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)) =
        Real.log ((n : ℝ) / x) := by field_simp
    rw [he, Real.exp_log (div_pos hnR hx)]
    push_cast
    field_simp
  have hint : (∫ u : ℝ, 𝓕 ψ (u / (2 * Real.pi))) = ∫ y in Ioi (0 : ℝ), Ψ y := by
    calc
      _ = ∫ u : ℝ, (Real.exp u : ℂ) * Ψ (Real.exp u) := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro u
        dsimp only
        rw [hψ]
        have he : 2 * Real.pi * (u / (2 * Real.pi)) = u := by field_simp
        rw [he]
      _ = _ := integral_exp_mul_comp_exp Ψ
  have ht := tendsto_tsum_tauberianFourierTerm hsum hf hG hG' ψ
  rw [hint] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [hsamp hx, tsum_div_const]

theorem tendsto_tsum_mul_smoothed_real {f : ℕ → ℝ} {C A : ℝ} {G : ℂ → ℂ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable (fun n => (f n : ℂ)) (σ : ℂ))
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : EqOn G (fun s => LSeries (fun n => (f n : ℂ)) s - (A : ℂ) / (s - 1))
      {s | 1 < s.re}) {Ψ : ℝ → ℝ} (hsm : ContDiff ℝ ∞ Ψ) (hs : HasCompactSupport Ψ)
    (hp : tsupport Ψ ⊆ Ioi 0) :
    Tendsto (fun x : ℝ => (∑' n : ℕ, f n * Ψ ((n : ℝ) / x)) / x) atTop
      (𝓝 (A * ∫ y in Ioi (0 : ℝ), Ψ y)) := by
  have hsumC : ∀ n, ∑ i ∈ Finset.range n, ‖(f i : ℂ)‖ ≤ C * n := by
    intro n
    simpa only [Complex.norm_real] using hsum n
  have hsmC : ContDiff ℝ ∞ (fun t => (Ψ t : ℂ)) := Complex.ofRealCLM.contDiff.comp hsm
  have hsC : HasCompactSupport (fun t => (Ψ t : ℂ)) :=
    hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hpC : tsupport (fun t => (Ψ t : ℂ)) ⊆ Ioi 0 := by
    have he : Function.support (fun t => (Ψ t : ℂ)) = Function.support Ψ := by
      ext t
      exact not_congr Complex.ofReal_eq_zero
    rw [tsupport, he]
    exact hp
  have ht := (Complex.continuous_re.tendsto _).comp
    (tendsto_tsum_mul_smoothed hsumC hf hG hG' hsmC hsC hpC)
  have hint : (∫ y in Ioi (0 : ℝ), (Ψ y : ℂ)) =
      Complex.ofReal (∫ y in Ioi (0 : ℝ), Ψ y) := integral_complex_ofReal
  rw [hint] at ht
  simpa only [Function.comp_def, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    ← Complex.ofReal_tsum, Complex.ofReal_re] using ht

end DirichletL
