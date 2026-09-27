import Analysis.FunctionsGPrimitiveContinuation
import Analysis.FunctionsGMonodromy

/-!
CDT v2, Lemma `14functions`: subtract continued normalized primitives with
the same original subtraction constants. For a closed original lift, the
trace difference is homogeneous and supplies all three difference integrands.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem GPrimitiveContinuation.primitive_sub_deriv
    {δ : C(unitInterval, zagierPullbackRegularSet)} {k0 k1 : ℂ}
    (C : GPrimitiveContinuation δ k0 k1) (j : Fin 3) {t s : unitInterval}
    (hδ : δ t = δ s) :
    deriv (C.primitive j t - C.primitive j s) =ᶠ[𝓝 (mobiusCoordinate (δ s : ℂ))]
      (fun y => (C.trace t y - C.trace s y) / y ^ (j : ℕ)) := by
  have hat : AnalyticAt ℂ (C.primitive j t) (mobiusCoordinate (δ s : ℂ)) := by
    simpa only [hδ] using (C.primitive_continuation j).analytic t
  have hdt : deriv (C.primitive j t) =ᶠ[𝓝 (mobiusCoordinate (δ s : ℂ))]
      gPrimitiveIntegrand (C.trace t) k0 k1 j := by
    simpa only [hδ] using C.primitive_deriv j t
  filter_upwards [hat.eventually_analyticAt,
    ((C.primitive_continuation j).analytic s).eventually_analyticAt,
    hdt, C.primitive_deriv j s] with y hat has hdt hds
  rw [deriv_sub hat.differentiableAt has.differentiableAt, hdt, hds, gPrimitiveIntegrand_sub]

/-- Literal initial germs and homogeneous difference integrands for every closed original lift. -/
theorem exists_gPrimitiveContinuation_loop (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ δ : C(unitInterval, zagierPullbackRegularSet),
      ‖(δ 0 : ℂ)‖ < R → δ 1 = δ 0 →
      ∃ C : GPrimitiveContinuation δ (gLinearCombinationAnalytic a b c 0)
          (deriv (gLinearCombinationAnalytic a b c) 0),
        (∀ i : Fin 7, C.functions i 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
          zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC)) i) ∧
        ((C.trace 1 - gLinearCombinationAnalytic a b c : ℂ → ℂ) :
          Germ (𝓝 (mobiusCoordinate (δ 0 : ℂ))) ℂ) ∈
            zagierSolutionGerms (mobiusCoordinate (δ 0 : ℂ)) ∧
        ∀ j : Fin 3, deriv (C.primitive j 1 -
          zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
            (j.castAdd 4)) =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
          (fun y => (C.trace 1 y - gLinearCombinationAnalytic a b c y) / y ^ (j : ℕ)) := by
  obtain ⟨R, hR, hC⟩ := exists_gPrimitiveContinuation_gLinearCombination a b c hrel
  obtain ⟨S, hS, hG⟩ := exists_analyticContinuationAlong_gLinearCombination_loop a b c hrel
  refine ⟨min R S, lt_min hR hS, ?_⟩
  intro δ hδ hloop
  obtain ⟨C, hC0, hP0⟩ := hC δ (hδ.trans_le (min_le_left _ _))
  obtain ⟨G, hGc, hG0, hGh⟩ := hG δ (hδ.trans_le (min_le_right _ _)) hloop
  refine ⟨C, C.functions_initial hC0 hP0, ?_, ?_⟩
  · have he : C.trace 1 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] G 1 := by
      simpa only [hloop] using
        C.trace_continuation.eq_of_preconnectedSpace hGc (t₀ := 0) (hC0.trans hG0.symm) 1
    have he' : C.trace 1 - gLinearCombinationAnalytic a b c =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
        G 1 - gLinearCombinationAnalytic a b c := he.sub Filter.EventuallyEq.rfl
    rw [Germ.coe_eq.mpr he']
    exact hGh
  · intro j
    have hp : C.primitive j 1 - C.primitive j 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
        C.primitive j 1 -
          zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • DirichletL.hC))
            (j.castAdd 4) := Filter.EventuallyEq.rfl.sub (hP0 j)
    apply hp.deriv.symm.trans ((C.primitive_sub_deriv j hloop).trans ?_)
    filter_upwards [hC0] with y hy
    rw [hy]

end DirichletL
