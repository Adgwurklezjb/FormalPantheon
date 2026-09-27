import Analysis.FunctionsGPrimitiveMonodromy
import Analysis.ZagierPullbackSeparation
import Analysis.ZagierAnalyticConjugacy

/-!
The two homogeneous sheet differences cannot cancel in CDT v2's trace
`defG`. This preserves nonzero actual H monodromy through the normalized
G primitives in Lemma `14functions` (TeX 8074-8100).
-/

namespace DirichletL

open Filter
open scoped Topology

theorem ForcedHTraceContinuation.trace_ne_of_left_ne
    {δ : C(unitInterval, zagierPullbackRegularSet)} {b c : ℂ}
    (C : ForcedHTraceContinuation δ b c) (s t : unitInterval) (hδ : δ s = δ t)
    (hne : ¬C.left s =ᶠ[𝓝 (δ t : ℂ)] C.left t) :
    ¬C.trace s =ᶠ[𝓝 (mobiusCoordinate (δ t : ℂ))] C.trace t := by
  intro he
  have hLs : AnalyticAt ℂ (C.left s) (δ t : ℂ) := by
    simpa only [hδ] using C.left_continuation.analytic s
  have hRs : AnalyticAt ℂ (C.right s) (mobiusAnalyticInvolution (δ t : ℂ)) := by
    simpa only [hδ] using C.right_continuation.analytic s
  have hLo := C.left_ode s
  have hRo := C.right_ode s
  rw [hδ] at hLo hRo
  have hLF := eventually_zagierSecondOrderODE_sub_eq_zero hLs (C.left_continuation.analytic t)
    (by
      filter_upwards [hLo, C.left_ode t] with z hs ht
      exact hs.trans ht.symm)
  have hRF := eventually_zagierSecondOrderODE_sub_eq_zero (C.right_continuation.analytic t) hRs
    (by
      filter_upwards [C.right_ode t, hRo] with z ht hs
      exact ht.trans hs.symm)
  have hLC := eventually_zagierConjugate_comp_mobiusAnalyticInvolution (δ t).property.1
    ((C.right_continuation.analytic t).sub hRs) hRF
  have hps := C.trace_pullback s
  rw [hδ] at hps
  have hdiff : C.left s - C.left t =ᶠ[𝓝 (δ t : ℂ)]
      (C.right t - C.right s) ∘ mobiusAnalyticInvolution := by
    filter_upwards [hps, C.trace_pullback t,
      he.comp_tendsto (analyticAt_mobiusCoordinate (δ t).property.1).continuousAt.tendsto]
      with z hs ht hz
    dsimp only [Function.comp_apply, Pi.sub_apply] at hs ht hz ⊢
    rw [hs, ht] at hz
    linear_combination hz
  have hz := eventuallyEq_zero_of_zagierSecondOrder_and_conjugate (δ t).property.1
    (δ t).property.2 (hLs.sub (C.left_continuation.analytic t)) hLF
    ((eventuallyEq_zagierConjugateAnalyticODE hdiff).trans hLC)
  apply hne
  filter_upwards [hz] with z hz
  exact sub_eq_zero.mp hz

theorem exists_gPrimitiveContinuation_nontrivial_of_H_loop (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ δ : C(unitInterval, zagierPullbackRegularSet),
      ‖(δ 0 : ℂ)‖ < R → δ 1 = δ 0 → ∀ F : unitInterval → ℂ → ℂ,
      AnalyticContinuationAlong (fun t => (δ t : ℂ)) F →
      F 0 =ᶠ[𝓝 (δ 0 : ℂ)] hLinearCombinationAnalytic a b c →
      (¬F 1 =ᶠ[𝓝 (δ 0 : ℂ)] F 0) →
      ∃ C : GPrimitiveContinuation δ (gLinearCombinationAnalytic a b c 0)
          (deriv (gLinearCombinationAnalytic a b c) 0),
        (∀ i : Fin 7, C.functions i 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
          zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC)) i) ∧
        (¬C.trace 1 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] gLinearCombinationAnalytic a b c) ∧
        ((C.trace 1 - gLinearCombinationAnalytic a b c : ℂ → ℂ) :
          Germ (𝓝 (mobiusCoordinate (δ 0 : ℂ))) ℂ) ∈
            zagierSolutionGerms (mobiusCoordinate (δ 0 : ℂ)) ∧
        ∀ j : Fin 3, deriv (C.primitive j 1 -
          zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
            (j.castAdd 4)) =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
          (fun y => (C.trace 1 y - gLinearCombinationAnalytic a b c y) / y ^ (j : ℕ)) := by
  obtain ⟨R, hR, hP⟩ := exists_gPrimitiveContinuation_loop a b c hrel
  obtain ⟨S, hS, hT⟩ := exists_forcedHTraceContinuation_gLinearCombination a b c hrel
  refine ⟨min R S, lt_min hR hS, ?_⟩
  intro δ hδ hloop F hF hF0 hFne
  obtain ⟨C, hC0, hCo, hCd⟩ := hP δ (hδ.trans_le (min_le_left _ _)) hloop
  obtain ⟨T, hT0, _, hTg⟩ := hT δ (hδ.trans_le (min_le_right _ _))
  have hTF : T.left 1 =ᶠ[𝓝 (δ 0 : ℂ)] F 1 := by
    simpa only [hloop] using T.left_continuation.eq_of_preconnectedSpace hF
      (t₀ := 0) (hT0.trans hF0.symm) 1
  have hTne : ¬T.left 1 =ᶠ[𝓝 (δ 0 : ℂ)] T.left 0 := by
    intro he
    exact hFne (hTF.symm.trans (he.trans (hT0.trans hF0.symm)))
  have hCg : C.trace 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] gLinearCombinationAnalytic a b c :=
    hC0 3
  have hCT : C.trace 1 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] T.trace 1 := by
    simpa only [hloop] using C.trace_continuation.eq_of_preconnectedSpace T.trace_continuation
      (t₀ := 0) (hCg.trans hTg.symm) 1
  refine ⟨C, hC0, ?_, hCo, hCd⟩
  intro he
  exact T.trace_ne_of_left_ne 1 0 hloop hTne (hCT.symm.trans (he.trans hTg.symm))

end DirichletL
