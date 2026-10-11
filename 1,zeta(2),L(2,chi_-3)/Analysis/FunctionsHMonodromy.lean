import Analysis.FunctionsHLocalMonodromy
import Analysis.AnalyticContinuationPaths
import Analysis.FunctionsHOverconvergence

/-!
Nonzero monodromy of the actual forced H germ in CDT v2, Proposition
`functionsH` and the nonzero-branch step of Lemma `14functions`. Transport
the proved local Wronskian periods to any regular base, retaining the
literal initial germ and both forcing constants.
-/

namespace DirichletL

open Filter unitInterval
open scoped Topology

/-- Every forced H germ with nonzero forcing changes along a constructed closed regular path. -/
theorem exists_forcedH_nontrivial_loop (x : zagierPullbackRegularSet) (b c : ℂ)
    (hbc : b ≠ 0 ∨ c ≠ 0) (H : ℂ → ℂ) (hH : AnalyticAt ℂ H (x : ℂ))
    (hHo : ∀ᶠ z in 𝓝 (x : ℂ), zagierSecondOrderODE H z = b + c / (1 - z)) :
    ∃ δ : Path x x, ∃ F : I → ℂ → ℂ,
      AnalyticContinuationAlong (fun t => (δ t : ℂ)) F ∧
      F 0 =ᶠ[𝓝 (x : ℂ)] H ∧
      (∀ t, ∀ᶠ z in 𝓝 (δ t : ℂ), zagierSecondOrderODE (F t) z = b + c / (1 - z)) ∧
      ¬F 1 =ᶠ[𝓝 (x : ℂ)] F 0 := by
  have hcircle : ∃ γ : C(I, zagierPullbackRegularSet), γ 1 = γ 0 ∧
      ∀ h : ℂ → ℂ, AnalyticAt ℂ h (γ 0 : ℂ) →
        (∀ᶠ z in 𝓝 (γ 0 : ℂ), zagierSecondOrderODE h z = b + c / (1 - z)) →
        ∃ W : I → ℂ → ℂ,
          AnalyticContinuationAlong (fun t => (γ t : ℂ)) W ∧
          W 0 =ᶠ[𝓝 (γ 0 : ℂ)] h ∧
          (∀ t, ∀ᶠ z in 𝓝 (γ t : ℂ), zagierSecondOrderODE (W t) z = b + c / (1 - z)) ∧
          ¬W 1 =ᶠ[𝓝 (γ 0 : ℂ)] W 0 := by
    rcases hbc with hb | hc
    · obtain ⟨ε, hε, he⟩ := exists_forcedH_reciprocalCircle_nontrivial b c hb
      obtain ⟨γ, _, hloop, hγ⟩ := he (ε / 2) (half_pos hε) (half_lt_self hε)
      exact ⟨γ, hloop, hγ⟩
    · obtain ⟨ε, hε, he⟩ := exists_forcedH_oneCircle_nontrivial b c hc
      obtain ⟨γ, _, hloop, hγ⟩ := he (ε / 2) (half_pos hε) (half_lt_self hε)
      exact ⟨γ, hloop, hγ⟩
  obtain ⟨γ, hloop, hγ⟩ := hcircle
  let τ : Path (γ 0) (γ 0) := ⟨γ, rfl, hloop⟩
  letI : PathConnectedSpace zagierPullbackRegularSet :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_zagierPullbackRegularSet
  let η := PathConnectedSpace.somePath x (γ 0)
  let δ := (η.trans τ).trans η.symm
  let ρ : C(I, hForcedRegularSet) := {
    toFun t := ⟨(δ t : ℂ), mem_hForcedRegularSet_of_mem_zagierPullbackRegularSet (δ t).property⟩
    continuous_toFun := (continuous_subtype_val.comp δ.continuous).subtype_mk _ }
  have hρ0 : (ρ 0 : ℂ) = (x : ℂ) := by
    change (δ 0 : ℂ) = (x : ℂ)
    rw [Path.source]
  obtain ⟨F, hF, hF0, hFo⟩ := exists_analyticContinuationAlong_forcedH ρ H b c
    (by simpa only [hρ0] using hH) (by simpa only [hρ0] using hHo)
  change AnalyticContinuationAlong (fun t => (δ t : ℂ)) F at hF
  change (∀ t, ∀ᶠ z in 𝓝 (δ t : ℂ), zagierSecondOrderODE (F t) z = b + c / (1 - z)) at hFo
  rw [hρ0] at hF0
  refine ⟨δ, F, hF, hF0, hFo, ?_⟩
  intro he
  let P (z : zagierPullbackRegularSet) (f : ℂ → ℂ) : Prop :=
    ∀ᶠ w in 𝓝 (z : ℂ), zagierSecondOrderODE f w = b + c / (1 - w)
  obtain ⟨U, V, hU, hV, hU0, hV1, hUV, hUP, _⟩ :=
    AnalyticContinuationAlong.exists_trans_parts (η.trans τ) η.symm Subtype.val hF P hFo
  obtain ⟨A, B, hA, hB, hA0, hB1, hAB, _, hBP⟩ :=
    AnalyticContinuationAlong.exists_trans_parts η τ Subtype.val hU P hUP
  have hVr : AnalyticContinuationAlong (fun t => (η t : ℂ)) (fun t => V (σ t)) := by
    simpa only [Function.comp_def, Path.symm_apply, unitInterval.symm_symm] using
      hV.reparam unitInterval.continuous_symm
  have hVr0 : (fun t => V (σ t)) 0 =ᶠ[𝓝 (η 0 : ℂ)] A 0 := by
    simpa only [unitInterval.symm_zero, Path.source, hV1, hA0, hU0] using he
  have hBE : B 1 =ᶠ[𝓝 (γ 0 : ℂ)] B 0 := by
    have hend := hVr.eq_of_preconnectedSpace hA hVr0 1
    simpa only [unitInterval.symm_one, Path.target, ← hUV, ← hB1, hAB] using hend
  have hBa : AnalyticAt ℂ (B 0) (γ 0 : ℂ) := by
    simpa only [Path.source] using hB.analytic 0
  have hBo : ∀ᶠ z in 𝓝 (γ 0 : ℂ), zagierSecondOrderODE (B 0) z = b + c / (1 - z) := by
    simpa only [P, Path.source] using hBP 0
  obtain ⟨W, hW, hW0, _, hWne⟩ := hγ (B 0) hBa hBo
  have hB' : AnalyticContinuationAlong (fun t => (γ t : ℂ)) B := hB
  have hWB := hW.eq_of_preconnectedSpace hB' hW0 1
  rw [hloop] at hWB
  exact hWne (hWB.trans (hBE.trans hW0.symm))

/-- The literal nonzero H combination has nontrivial closed-loop continuation at every such base. -/
theorem exists_hLinearCombination_nontrivial_loop (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) (x : zagierPullbackRegularSet) (hx : ‖(x : ℂ)‖ < 1) :
    ∃ δ : Path x x, ∃ F : I → ℂ → ℂ,
      AnalyticContinuationAlong (fun t => (δ t : ℂ)) F ∧
      F 0 =ᶠ[𝓝 (x : ℂ)] hLinearCombinationAnalytic a b c ∧
      (∀ t, ∀ᶠ z in 𝓝 (δ t : ℂ), zagierSecondOrderODE (F t) z =
        (b : ℂ) + (c : ℂ) / (1 - z)) ∧
      ¬F 1 =ᶠ[𝓝 (x : ℂ)] F 0 := by
  have hbc : (b : ℂ) ≠ 0 ∨ (c : ℂ) ≠ 0 := by
    by_cases hb : (b : ℂ) = 0
    · right
      intro hc
      have hbq : b = 0 := by exact_mod_cast hb
      have hcq : c = 0 := by exact_mod_cast hc
      have har : (a : ℝ) = 0 := by
        simpa only [hbq, hcq, Rat.cast_zero, zero_mul, add_zero] using hrel
      have haq : a = 0 := by exact_mod_cast har
      exact hne ⟨haq, hbq, hcq⟩
    · exact Or.inl hb
  apply exists_forcedH_nontrivial_loop x b c hbc (hLinearCombinationAnalytic a b c)
    (analyticAt_hLinearCombinationAnalytic a b c hrel hx)
  filter_upwards [continuous_norm.continuousAt.eventually_lt_const hx] with z hz
  exact hLinearCombinationAnalytic_ode a b c hrel hz

end DirichletL
