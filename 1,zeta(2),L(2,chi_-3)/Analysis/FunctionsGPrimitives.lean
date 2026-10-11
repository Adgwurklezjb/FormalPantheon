import Analysis.FunctionsGAnalytic
import Analysis.ZagierAuxiliary

/-!
The literal normalized G primitives in CDT v2, Lemma `14functions`.
The existing seven-function family supplies the initial functions; the
integrand interface keeps the original subtraction constants explicit.
-/

namespace DirichletL

open Filter
open scoped Topology ENNReal

/-- The three primitive integrands with fixed original subtraction constants. -/
noncomputable def gPrimitiveIntegrand (G : ℂ → ℂ) (k0 k1 : ℂ) : Fin 3 → ℂ → ℂ :=
  ![G, fun y => (G y - k0) / y, fun y => (G y - k0 - k1 * y) / y ^ 2]

theorem gPrimitiveIntegrand_sub (G H : ℂ → ℂ) (k0 k1 : ℂ) (j : Fin 3) (y : ℂ) :
    gPrimitiveIntegrand G k0 k1 j y - gPrimitiveIntegrand H k0 k1 j y =
      (G y - H y) / y ^ (j : ℕ) := by
  fin_cases j <;> simp [gPrimitiveIntegrand, div_sub_div_same]

/-- Away from zero the existing removable integrands equal the literal quotients. -/
theorem hasDerivAt_zagierAuxiliaryFunctions_integrals_of_ne (f : PowerSeries ℚ) {r : ℝ≥0∞}
    (hr0 : 0 < r) (hr : r ≤ (complexSeries f).radius) (j : Fin 3)
    {y : ℂ} (hy : y ∈ EMetric.ball 0 r) (hy0 : y ≠ 0) :
    HasDerivAt (zagierAuxiliaryFunctions f (j.castAdd 4))
      (gPrimitiveIntegrand (complexSeries f).sum ((complexSeries f).sum 0)
        (deriv (complexSeries f).sum 0) j y) y := by
  have hd := (hasDerivAt_zagierAuxiliaryFunctions_integrals f hr0 hr j hy).differentiableAt
  apply hd.hasDerivAt.congr_deriv
  fin_cases j
  · exact (hasDerivAt_zagierAuxiliaryFunctions_integrals f hr0 hr 0 hy).deriv
  · exact deriv_zagierAuxiliaryFunctions_one f hr0 hr hy hy0
  · exact deriv_zagierAuxiliaryFunctions_two f hr0 hr hy hy0

/-- One positive neighborhood supplies both H branches and all seven literal initial germs. -/
theorem exists_gPrimitives_initial_radius (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : ℂ, ‖x‖ < R →
      ‖x‖ < 1 ∧ ‖mobiusAnalyticInvolution x‖ < 1 ∧
      (∀ j : Fin 7, AnalyticAt ℂ
        (zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC)) j)
        (mobiusCoordinate x)) ∧
      (gLinearCombinationAnalytic a b c ∘ mobiusCoordinate) =ᶠ[𝓝 x]
        (fun z => hLinearCombinationAnalytic a b c z +
          hLinearCombinationAnalytic a b c (mobiusAnalyticInvolution z)) ∧
      (∀ j : Fin 3, x ≠ 0 → HasDerivAt
        (zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
          (j.castAdd 4))
        (gPrimitiveIntegrand (gLinearCombinationAnalytic a b c)
          (gLinearCombinationAnalytic a b c 0) (deriv (gLinearCombinationAnalytic a b c) 0)
          j (mobiusCoordinate x)) (mobiusCoordinate x)) ∧
      (x ≠ 0 → x ∈ zagierPullbackRegularSet) := by
  let F := symmetrizedDescent (a • hA + b • hB + c • hC)
  have hr : 0 < (complexSeries F).radius :=
    pos_radius_complexSeries_symmetrizedDescent _
      (zero_lt_one.trans_le (one_le_radius_h_linearCombination a b c hrel))
  obtain ⟨R, hR, hinit⟩ := exists_gLinearCombination_initial_radius a b c hrel
  have hY : Tendsto mobiusCoordinate (𝓝 (0 : ℂ)) (𝓝 0) := by
    simpa only [mobiusCoordinate_zero] using
      (analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1)).continuousAt.tendsto
  obtain ⟨S, hS, hball⟩ := Metric.mem_nhds_iff.mp
    (hY.eventually (EMetric.ball_mem_nhds (0 : ℂ) hr))
  refine ⟨min R S, lt_min hR hS, ?_⟩
  intro x hx
  obtain ⟨hx1, hw1, _, he, hreg⟩ := hinit x (hx.trans_le (min_le_left _ _))
  have hy : mobiusCoordinate x ∈ EMetric.ball 0 (complexSeries F).radius :=
    hball (by simpa only [Metric.mem_ball, dist_zero_right] using
      hx.trans_le (min_le_right R S))
  refine ⟨hx1, hw1, fun j => analyticAt_zagierAuxiliaryFunctions F hr le_rfl j hy,
    he, ?_, hreg⟩
  intro j hx0
  have hy0 := ((mem_zagierODERegularSet_iff _).mp (hreg hx0).2).1
  simpa only [F, gLinearCombinationAnalytic, symmetrizedAnalytic] using
    hasDerivAt_zagierAuxiliaryFunctions_integrals_of_ne F hr le_rfl j hy hy0

end DirichletL
