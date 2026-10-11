import Analysis.FunctionsHMonodromy
import Analysis.FunctionsHPathContinuation
import Analysis.ZagierOriginalShears
import Analysis.ZagierSourceOrbit
import Analysis.FunctionsGMonodromy

/-!
Select an actual changed endpoint conjugate for CDT v2, Lemma `14functions`
(TeX 8074-8100). The two proved shears detect a nonzero actual H difference;
the original path, exact endpoint circle, and fixed forcing are retained.
-/

namespace DirichletL

open Filter Set unitInterval
open scoped Topology

theorem exists_forcedH_endpoint_conjugate {p : ℝ} (hp : p ∈ Ioo 0 (1 / 9 : ℝ))
    (H : ℂ → ℂ) (b c : ℂ) (hbc : b ≠ 0 ∨ c ≠ 0)
    (hH : ∀ z, ‖z‖ < 1 → AnalyticAt ℂ H z)
    (hHo : ∀ z, ‖z‖ < 1 → zagierSecondOrderODE H z = b + c / (1 - z))
    {R : ℝ} (hR : 0 < R) :
    ∃ q : ℝ, ∃ hq : q ∈ Ioo 0 (1 / 9 : ℝ), ∃ r : ℝ, ∃ hr : r ∈ Ioo 0 (1 / 9 : ℝ),
      r < R ∧ q = (1 - 9 * r) / (9 * (1 - r)) ∧
      ∃ τ : Path (⟨q, zagierEndpointInterval_mem_pullback hq⟩ : zagierPullbackRegularSet)
          ⟨q, zagierEndpointInterval_mem_pullback hq⟩,
        (∀ t, (τ t : ℂ) = zagierEndpointCirclePath r hr t) ∧
        ∃ η : Path (⟨p, zagierEndpointInterval_mem_pullback hp⟩ : zagierPullbackRegularSet)
            ⟨q, zagierEndpointInterval_mem_pullback hq⟩, ∃ F : I → ℂ → ℂ,
          AnalyticContinuationAlong (fun t => (((η.trans τ).trans η.symm) t : ℂ)) F ∧
          F 0 =ᶠ[𝓝 (p : ℂ)] H ∧
          (∀ t, ∀ᶠ z in 𝓝 (((η.trans τ).trans η.symm) t : ℂ),
            zagierSecondOrderODE (F t) z = b + c / (1 - z)) ∧
          ¬F 1 =ᶠ[𝓝 (p : ℂ)] F 0 := by
  let x : zagierPullbackRegularSet := ⟨p, zagierEndpointInterval_mem_pullback hp⟩
  let base := zagierPullbackProjection x
  have hnorm {s : ℝ} (hs : s ∈ Ioo 0 (1 / 9 : ℝ)) : ‖(s : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
    linarith [hs.2]
  have hHe {z : ℂ} (hz : ‖z‖ < 1) :
      ∀ᶠ w in 𝓝 z, zagierSecondOrderODE H w = b + c / (1 - w) := by
    filter_upwards [continuous_norm.continuousAt.eventually_lt_const hz] with w hw
    exact hHo w hw
  obtain ⟨q, hq, r, hr, hrR, hqr, τ, hτ, hτnorm, l, hl, hτshear⟩ :=
    exists_zagierOriginal_endpoint_shear_lt base hR
  let y : zagierPullbackRegularSet := ⟨q, zagierEndpointInterval_mem_pullback hq⟩
  obtain ⟨U, hUnorm, k, hk, hUshear⟩ := exists_zagierOriginal_origin_shear hq base
  obtain ⟨φ, ψ, hφ, hψ, hind⟩ := exists_zagierEndpointSolutionGerms hq
  obtain ⟨hUφ, hUψ⟩ := hUshear φ ψ hφ hψ
  obtain ⟨hτφ, hτψ⟩ := hτshear φ ψ hφ hψ
  have hconst {u v : zagierPullbackRegularSet} (γ : Path u v)
      (hn : ∀ t, ‖(γ t : ℂ)‖ < 1) :
      AnalyticContinuationAlong (fun t => (γ t : ℂ)) (fun _ => H) :=
    AnalyticContinuationAlong.const (continuous_subtype_val.comp γ.continuous)
      (fun t => hH _ (hn t))
  let Good (η : Path x y) : Prop := ∃ F : I → ℂ → ℂ,
    AnalyticContinuationAlong (fun t => (((η.trans τ).trans η.symm) t : ℂ)) F ∧
    F 0 =ᶠ[𝓝 (p : ℂ)] H ∧
    (∀ t, ∀ᶠ z in 𝓝 (((η.trans τ).trans η.symm) t : ℂ),
      zagierSecondOrderODE (F t) z = b + c / (1 - z)) ∧
    ¬F 1 =ᶠ[𝓝 (p : ℂ)] F 0
  have hfinish (η : Path x y) (W : I → ℂ → ℂ)
      (hW : AnalyticContinuationAlong (fun t => (η t : ℂ)) W)
      (hW0 : W 0 =ᶠ[𝓝 (p : ℂ)] H)
      (hWo : ∀ᶠ z in 𝓝 (q : ℂ), zagierSecondOrderODE (W 1) z = b + c / (1 - z))
      (χ : zagierSolutionGerms (mobiusCoordinate q))
      (hχ : mobiusGermPullback y.property.1 (χ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = W 1 - H)
      (hne : zagierPathTransport base (τ.map zagierPullbackProjection.continuous) χ ≠ χ) :
      Good η := by
    have hW1 : AnalyticAt ℂ (W 1) (q : ℂ) := by
      simpa only [Path.target] using hW.analytic 1
    obtain ⟨T, hT, hT0, _⟩ := exists_analyticContinuationAlong_forcedH_path τ (W 1) b c hW1 hWo
    have hχT : mobiusGermPullback y.property.1
        (χ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = T 0 - H :=
      hχ.trans (Germ.coe_eq.mpr (hT0.symm.sub Filter.EventuallyEq.rfl))
    have htransport := mobiusGermPullback_zagierOriginalPathTransport base τ
      (hT.sub (hconst τ hτnorm)) χ hχT
    have hTne : ¬T 1 =ᶠ[𝓝 (q : ℂ)] T 0 := by
      intro he
      apply hne
      apply Subtype.ext
      apply mobiusGermPullback_injective (zagierEndpointInterval_noncritical hq).1
        y.property.1 (zagierEndpointInterval_noncritical hq).2.2
      exact htransport.trans ((Germ.coe_eq.mpr (he.sub Filter.EventuallyEq.rfl)).trans hχT.symm)
    exact exists_forcedH_conjugate_nontrivial η τ H b c (hH _ (hnorm hp)) (hHe (hnorm hp))
      hW hT hW0 hT0 hTne
  obtain ⟨ξ, Z, hZ, hZ0, _, hZne⟩ :=
    exists_forcedH_nontrivial_loop y b c hbc H (hH _ (hnorm hq)) (hHe (hnorm hq))
  let β := zagierPullbackIntervalPath hp hq
  let η := β.trans ξ
  obtain ⟨W, hW, hW0, hWo⟩ :=
    exists_analyticContinuationAlong_forcedH_path η H b c (hH _ (hnorm hp)) (hHe (hnorm hp))
  have hWZ : W 1 =ᶠ[𝓝 (q : ℂ)] Z 1 := hW.trans_end_eq β ξ Subtype.val
    (hconst β (norm_zagierPullbackIntervalPath_lt_one hp hq)) hZ hW0 hZ0.symm
  have hWne : ¬W 1 =ᶠ[𝓝 (q : ℂ)] H := by
    intro he
    exact hZne (hWZ.symm.trans (he.trans hZ0.symm))
  have hW1 : AnalyticAt ℂ (W 1) (q : ℂ) := by
    simpa only [Path.target] using hW.analytic 1
  have hWo1 : ∀ᶠ z in 𝓝 (q : ℂ), zagierSecondOrderODE (W 1) z = b + c / (1 - z) := by
    simpa only [Path.target] using hWo 1
  have hdiff := eventually_zagierSecondOrderODE_sub_eq_zero hW1 (hH _ (hnorm hq))
    (by
      filter_upwards [hWo1, hHe (hnorm hq)] with z hw hz
      exact hw.trans hz.symm)
  obtain ⟨χ, hχ⟩ := exists_zagierSolutionGerm_mobiusPullback
    (zagierEndpointInterval_noncritical hq).1 (zagierEndpointInterval_noncritical hq).2.1
    (zagierEndpointInterval_noncritical hq).2.2 (hW1.sub (hH _ (hnorm hq))) hdiff
  have hχne : χ ≠ 0 := by
    intro he
    have hz : ((W 1 - H : ℂ → ℂ) : Germ (𝓝 (q : ℂ)) ℂ) = 0 := by
      rw [← hχ, he]
      simp only [Submodule.coe_zero, map_zero]
    apply hWne
    filter_upwards [Germ.coe_eq.mp hz] with z hz
    exact sub_eq_zero.mp hz
  have hχspan : χ ∈ Submodule.span ℂ {φ, ψ} := by
    rw [← zagierSourceSummand_eq_span_endpoint hq φ ψ hφ hψ]
    exact ⟨W 1 - H, hW1.sub (hH _ (hnorm hq)), hdiff, hχ⟩
  have hm := not_fixed_of_two_linear_shears
    (zagierPathTransportLinearMap base (U.map zagierPullbackProjection.continuous))
    (zagierPathTransportLinearMap base (τ.map zagierPullbackProjection.continuous))
    hUφ hUψ hτφ hτψ hk hl hind hχspan hχne
  refine ⟨q, hq, r, hr, hrR, hqr, τ, hτ, ?_⟩
  change ∃ η : Path x y, Good η
  rcases hm with hm | hm
  · exact ⟨η, hfinish η W hW hW0 hWo1 χ hχ hm⟩
  · obtain ⟨A, hA, hA0, _⟩ :=
      exists_analyticContinuationAlong_forcedH_path U (W 1) b c hW1 hWo1
    have hχA : mobiusGermPullback y.property.1
        (χ : Germ (𝓝 (mobiusCoordinate q)) ℂ) = A 0 - H :=
      hχ.trans (Germ.coe_eq.mpr (hA0.symm.sub Filter.EventuallyEq.rfl))
    have hUA := mobiusGermPullback_zagierOriginalPathTransport base U
      (hA.sub (hconst U hUnorm)) χ hχA
    obtain ⟨B, hB, hB0, hBo⟩ := exists_analyticContinuationAlong_forcedH_path (η.trans U) H b c
      (hH _ (hnorm hp)) (hHe (hnorm hp))
    have hBA : B 1 =ᶠ[𝓝 (q : ℂ)] A 1 :=
      hB.trans_end_eq η U Subtype.val hW hA (hB0.trans hW0.symm) hA0.symm
    refine ⟨η.trans U, hfinish (η.trans U) B hB hB0
      (by simpa only [Path.target] using hBo 1)
      (zagierPathTransport base (U.map zagierPullbackProjection.continuous) χ) ?_ hm⟩
    exact hUA.trans (Germ.coe_eq.mpr (hBA.symm.sub Filter.EventuallyEq.rfl))

theorem exists_hLinearCombination_endpoint_conjugate (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) {p : ℝ} (hp : p ∈ Ioo 0 (1 / 9 : ℝ))
    {R : ℝ} (hR : 0 < R) :
    ∃ q : ℝ, ∃ hq : q ∈ Ioo 0 (1 / 9 : ℝ), ∃ r : ℝ, ∃ hr : r ∈ Ioo 0 (1 / 9 : ℝ),
      r < R ∧ q = (1 - 9 * r) / (9 * (1 - r)) ∧
      ∃ τ : Path (⟨q, zagierEndpointInterval_mem_pullback hq⟩ : zagierPullbackRegularSet)
          ⟨q, zagierEndpointInterval_mem_pullback hq⟩,
        (∀ t, (τ t : ℂ) = zagierEndpointCirclePath r hr t) ∧
        ∃ η : Path (⟨p, zagierEndpointInterval_mem_pullback hp⟩ : zagierPullbackRegularSet)
            ⟨q, zagierEndpointInterval_mem_pullback hq⟩, ∃ F : I → ℂ → ℂ,
          AnalyticContinuationAlong (fun t => (((η.trans τ).trans η.symm) t : ℂ)) F ∧
          F 0 =ᶠ[𝓝 (p : ℂ)] hLinearCombinationAnalytic a b c ∧
          (∀ t, ∀ᶠ z in 𝓝 (((η.trans τ).trans η.symm) t : ℂ),
            zagierSecondOrderODE (F t) z = (b : ℂ) + (c : ℂ) / (1 - z)) ∧
          ¬F 1 =ᶠ[𝓝 (p : ℂ)] F 0 := by
  have hbc : (b : ℂ) ≠ 0 ∨ (c : ℂ) ≠ 0 := by
    by_cases hb : (b : ℂ) = 0
    · right
      intro hc
      have hbq : b = 0 := by exact_mod_cast hb
      have hcq : c = 0 := by exact_mod_cast hc
      have har : (a : ℝ) = 0 := by
        simpa only [hbq, hcq, Rat.cast_zero, zero_mul, add_zero] using hrel
      exact hne ⟨by exact_mod_cast har, hbq, hcq⟩
    · exact Or.inl hb
  exact exists_forcedH_endpoint_conjugate hp (hLinearCombinationAnalytic a b c) b c hbc
    (fun _ hz => analyticAt_hLinearCombinationAnalytic a b c hrel hz)
    (fun _ hz => hLinearCombinationAnalytic_ode a b c hrel hz) hR

end DirichletL
