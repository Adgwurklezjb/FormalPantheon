import Analysis.FunctionsGOriginalRegularity

/-!
Actual integrands for the original-coordinate normalized G primitives.
Source: CDT v2 `defG` and `14functions`, TeX 7861-7866 and 8044-8051.
Prior meanings and the central update:
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The literal original-coordinate integrand with its analytic central value. -/
noncomputable def gPrimitiveOriginalIntegrand (a b c : ℚ) (j : Fin 3) : ℂ → ℂ := by
  classical
  exact Function.update
    (fun x => deriv mobiusCoordinate x *
      gPrimitiveIntegrand (fun _ => hLinearCombinationAnalytic a b c x +
        hLinearCombinationAnalytic a b c (mobiusAnalyticInvolution x))
        (gLinearCombinationAnalytic a b c 0) (deriv (gLinearCombinationAnalytic a b c) 0)
        j (mobiusCoordinate x))
    0 (deriv (fun x =>
      zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
        (j.castAdd 4) (mobiusCoordinate x)) 0)

theorem gPrimitiveOriginalIntegrand_eq_of_ne (a b c : ℚ) (j : Fin 3)
    {x : ℂ} (hx : x ≠ 0) :
    gPrimitiveOriginalIntegrand a b c j x = deriv mobiusCoordinate x *
      gPrimitiveIntegrand (fun _ => hLinearCombinationAnalytic a b c x +
        hLinearCombinationAnalytic a b c (mobiusAnalyticInvolution x))
        (gLinearCombinationAnalytic a b c 0) (deriv (gLinearCombinationAnalytic a b c) 0)
        j (mobiusCoordinate x) := by
  classical
  exact Function.update_of_ne hx _ _

theorem gPrimitiveOriginalIntegrand_eventuallyEq_deriv (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (j : Fin 3) :
    gPrimitiveOriginalIntegrand a b c j =ᶠ[𝓝 (0 : ℂ)]
      deriv (fun x =>
        zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
          (j.castAdd 4) (mobiusCoordinate x)) := by
  classical
  obtain ⟨R, hR, hinit⟩ := exists_gPrimitives_initial_radius a b c hrel
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hR] with x hx
  by_cases hx0 : x = 0
  · subst x
    simp [gPrimitiveOriginalIntegrand]
  · obtain ⟨_, _, _, he, hJ, hreg⟩ := hinit x (by simpa using hx)
    have hval : gLinearCombinationAnalytic a b c (mobiusCoordinate x) =
        hLinearCombinationAnalytic a b c x +
          hLinearCombinationAnalytic a b c (mobiusAnalyticInvolution x) :=
      he.self_of_nhds
    have hd := (hJ j hx0).comp x
      (analyticAt_mobiusCoordinate (hreg hx0).1).differentiableAt.hasDerivAt
    rw [gPrimitiveOriginalIntegrand_eq_of_ne a b c j hx0]
    fin_cases j <;> simpa [gPrimitiveIntegrand, hval, mul_comm] using hd.deriv.symm

theorem analyticOnNhd_gPrimitiveOriginalIntegrand (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (j : Fin 3) :
    AnalyticOnNhd ℂ (gPrimitiveOriginalIntegrand a b c j) (Metric.ball 0 (1 / 2)) := by
  intro x hx
  have hxn : ‖x‖ < 1 / 2 := by simpa using hx
  by_cases hx0 : x = 0
  · subst x
    obtain ⟨R, hR, hinit⟩ := exists_gPrimitives_initial_radius a b c hrel
    have hJ := (hinit 0 (by simpa only [norm_zero] using hR)).2.2.1 (j.castAdd 4)
    have hcomp := hJ.comp' (f := mobiusCoordinate)
      (analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1))
    exact hcomp.deriv.congr (gPrimitiveOriginalIntegrand_eventuallyEq_deriv a b c hrel j).symm
  · have hx1 : x ≠ 1 := by
      intro he
      simp only [he, norm_one] at hxn
      norm_num at hxn
    have hi := analyticAt_mobiusAnalyticInvolution hx1
    have hY := analyticAt_mobiusCoordinate hx1
    have hY0 := mobiusCoordinate_ne_zero hx0 hx1
    have hH := analyticAt_hLinearCombinationAnalytic a b c hrel
      (hxn.trans (by norm_num : (1 / 2 : ℝ) < 1))
    have hW := (analyticAt_hLinearCombinationAnalytic a b c hrel
      (norm_mobiusAnalyticInvolution_lt_one hxn)).comp' hi
    have hT := hH.add hW
    have heq : gPrimitiveOriginalIntegrand a b c j =ᶠ[𝓝 x]
        (fun w => deriv mobiusCoordinate w *
          gPrimitiveIntegrand (fun _ => hLinearCombinationAnalytic a b c w +
            hLinearCombinationAnalytic a b c (mobiusAnalyticInvolution w))
            (gLinearCombinationAnalytic a b c 0) (deriv (gLinearCombinationAnalytic a b c) 0)
            j (mobiusCoordinate w)) := by
      filter_upwards [eventually_ne_nhds hx0] with w hw
      exact gPrimitiveOriginalIntegrand_eq_of_ne a b c j hw
    apply AnalyticAt.congr _ heq.symm
    fin_cases j
    · exact hY.deriv.mul hT
    · exact hY.deriv.mul ((hT.sub analyticAt_const).div hY hY0)
    · exact hY.deriv.mul (((hT.sub analyticAt_const).sub
        (analyticAt_const.mul hY)).div (hY.pow 2) (pow_ne_zero 2 hY0))

end DirichletL
