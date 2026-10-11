import Analysis.FunctionsGOriginalIntegrands
import Analysis.AnalyticPrimitivesOnBalls

/-!
Actual normalized original-coordinate primitives for CDT v2 `14functions`.
Source: supplied TeX 8044-8051, with `defG` at 7861-7866.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem exists_analytic_gPrimitiveOriginal (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ K : Fin 3 → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (K j) (Metric.ball 0 (1 / 2))) ∧
      (∀ j, K j 0 = 0) ∧
      (∀ j x, ‖x‖ < 1 / 2 → HasDerivAt (K j) (gPrimitiveOriginalIntegrand a b c j x) x) ∧
      ∀ j, K j =ᶠ[𝓝 (0 : ℂ)] fun x =>
        zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
          (j.castAdd 4) (mobiusCoordinate x) := by
  classical
  choose K hKa hK0 hKd using fun j : Fin 3 => exists_analytic_primitive_on_ball
    (by norm_num : (0 : ℝ) < 1 / 2) (analyticOnNhd_gPrimitiveOriginalIntegrand a b c hrel j)
  refine ⟨K, hKa, hK0, fun j x hx => hKd j x (by simpa using hx), ?_⟩
  intro j
  let J (x : ℂ) :=
    zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
      (j.castAdd 4) (mobiusCoordinate x)
  obtain ⟨R, hR, hinit⟩ := exists_gPrimitives_initial_radius a b c hrel
  have hJ0 : AnalyticAt ℂ J 0 :=
    ((hinit 0 (by simpa only [norm_zero] using hR)).2.2.1 (j.castAdd 4)).comp'
      (f := mobiusCoordinate) (analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1))
  have hderiv : ∀ᶠ x in 𝓝 (0 : ℂ), HasDerivAt (fun w => K j w - J w) 0 x := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2),
      hJ0.eventually_analyticAt, gPrimitiveOriginalIntegrand_eventuallyEq_deriv a b c hrel j]
      with x hx hJx hIx
    have hJd : HasDerivAt J (gPrimitiveOriginalIntegrand a b c j x) x := by
      rw [hIx]
      exact hJx.differentiableAt.hasDerivAt
    simpa only [sub_self] using (hKd j x hx).sub hJd
  have hJzero : J 0 = 0 := by
    simpa only [J, mobiusCoordinate_zero] using zagierAuxiliaryFunctions_integrals_zero
      (symmetrizedDescent (a • hA + b • hB + c • hC)) j
  filter_upwards [eventuallyEq_const_of_eventually_hasDerivAt_zero hderiv] with x hx
  apply sub_eq_zero.mp
  simpa only [hK0 j, hJzero, sub_self] using hx

end DirichletL
