import Analysis.FunctionsGOriginalState
import Analysis.AnalyticLinearODEAnnulus
import Analysis.ContourQuadraticLift

/-!
Actual G trace and primitive pullbacks on the double parameter disc.
Source: CDT v2 TeX 1739-1744, 7157-7197, and `14functions` at 8044-8051.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_analytic_cdtContour_gPrimitive_double_pullback (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ F : Fin 4 → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball 0 1)) ∧
      ∀ j, F j =ᶠ[𝓝 (0 : ℂ)] fun z =>
        zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
          (j.castAdd 3) (cdtContourMap (z ^ 2)) := by
  obtain ⟨X, hXa, hX0, hX1, hXzero, hY, _, hXsmall⟩ :=
    exists_analytic_cdtContour_original_coordinate
  have hXat (z : ℂ) (hz : ‖z‖ < 1) : AnalyticAt ℂ X z := hXa z (by simpa using hz)
  have hreg (z : ℂ) (hza : (1 / 60 : ℝ) < ‖z‖) (hz : ‖z‖ < 1) :
      X z ≠ 0 ∧ X z ≠ 1 ∧ X z ≠ 1 / 9 ∧ X z ≠ -1 / 8 := by
    have hz0 : z ≠ 0 := by
      intro he
      simp only [he, norm_zero] at hza
      norm_num at hza
    refine ⟨fun he => hz0 ((hXzero z hz).mp he), hX1 z hz, ?_, ?_⟩
    · intro he
      have hv : cdtContourMap (z ^ 2) = -1 / 72 := by
        rw [← hY z hz, he, mobiusCoordinate_one_div_nine]
      exact (not_lt_of_ge hza.le) (norm_lt_one_div_sixty_of_cdtContourMap_sq_eq hz.le hv)
    · intro he
      have hv : cdtContourMap (z ^ 2) = -1 / 72 := by
        rw [← hY z hz, he]
        norm_num [mobiusCoordinate]
      exact (not_lt_of_ge hza.le) (norm_lt_one_div_sixty_of_cdtContourMap_sq_eq hz.le hv)
  let M (z : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
    deriv X z • gPrimitiveMatrix (b : ℂ) (c : ℂ)
      (gLinearCombinationAnalytic a b c 0) (deriv (gLinearCombinationAnalytic a b c) 0) (X z)
  have hM : AnalyticOnNhd ℂ M {z : ℂ | (1 / 60 : ℝ) < ‖z‖ ∧ ‖z‖ < 1} := by
    intro z hz
    obtain ⟨hx0, hx1, hx9, hx8⟩ := hreg z hz.1 hz.2
    exact (hXat z hz.2).deriv.smul ((analyticAt_gPrimitiveMatrix_of_ne
      (b : ℂ) (c : ℂ) (gLinearCombinationAnalytic a b c 0)
      (deriv (gLinearCombinationAnalytic a b c) 0) hx0 hx1 hx9 hx8).comp' (hXat z hz.2))
  obtain ⟨v, hva, hvgerm, hvo⟩ := exists_analytic_gPrimitiveOriginal_state a b c hrel
  have hvX : AnalyticOnNhd ℂ (fun z => v (X z)) (Metric.ball 0 (1 / 50)) := by
    intro z hz
    have hzn : ‖z‖ < 1 / 50 := by simpa using hz
    exact (hva (X z) (by simpa using hXsmall z hzn)).comp'
      (hXat z (hzn.trans (by norm_num)))
  have hvoX (z : ℂ) (hza : (1 / 60 : ℝ) < ‖z‖) (hzr : ‖z‖ < 1 / 50) :
      HasDerivAt (fun w => v (X w)) (M z *ᵥ v (X z)) z := by
    have hz1 : ‖z‖ < 1 := hzr.trans (by norm_num)
    obtain ⟨hx0, _, hx9, hx8⟩ := hreg z hza hz1
    simpa only [M, Matrix.smul_mulVec_assoc, Function.comp_apply] using
      (hvo (X z) (hXsmall z hzr) hx0 hx9 hx8).scomp z
        (hXat z hz1).differentiableAt.hasDerivAt
  obtain ⟨V, hVa, hVeq, _⟩ := exists_analytic_matrix_extension_on_ball
    (by norm_num : (0 : ℝ) < 1 / 60) (by norm_num : (1 / 60 : ℝ) < 1 / 50)
    (by norm_num : (1 / 50 : ℝ) < 1) hM hvX hvoX
  have hXt : Tendsto X (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
    simpa only [hX0] using (hXat 0 (by norm_num)).continuousAt.tendsto
  have hVlocal : V =ᶠ[𝓝 (0 : ℂ)] fun z => v (X z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 50)]
      with z hz
    exact hVeq hz
  have hVgerm := hVlocal.trans (hvgerm.comp_tendsto hXt)
  have hYgerm : ∀ᶠ z in 𝓝 (0 : ℂ), mobiusCoordinate (X z) = cdtContourMap (z ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
    exact hY z (by simpa using hz)
  let F : Fin 4 → ℂ → ℂ := fun j z => ![V z 5, V z 6, V z 7, V z 0 + V z 2] j
  have hprimitives (j : Fin 3) : F (j.castAdd 1) =ᶠ[𝓝 (0 : ℂ)] fun z =>
      zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
        (j.castAdd 4) (cdtContourMap (z ^ 2)) := by
    filter_upwards [hVgerm, hYgerm] with z hzV hzY
    have h := congrArg (fun s : Fin 8 → ℂ => s (Fin.natAdd 5 j)) hzV
    dsimp only [Function.comp_apply] at h
    rw [gPrimitiveState_integrals, hzY] at h
    fin_cases j <;> simpa [F] using h
  have htrace : F 3 =ᶠ[𝓝 (0 : ℂ)] fun z =>
      zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
        3 (cdtContourMap (z ^ 2)) := by
    filter_upwards [hVgerm, hYgerm,
      (gLinearCombinationAnalytic_pullback a b c hrel).comp_tendsto hXt]
      with z hzV hzY hzG
    change V z 0 + V z 2 = gLinearCombinationAnalytic a b c (cdtContourMap (z ^ 2))
    rw [hzV]
    change hLinearCombinationAnalytic a b c (X z) +
      hLinearCombinationAnalytic a b c (mobiusAnalyticInvolution (X z)) = _
    simpa only [Function.comp_apply, hzY] using hzG.symm
  refine ⟨F, ?_, ?_⟩
  · intro j z hz
    fin_cases j
    · exact analyticAt_pi_iff.mp (hVa z hz) 5
    · exact analyticAt_pi_iff.mp (hVa z hz) 6
    · exact analyticAt_pi_iff.mp (hVa z hz) 7
    · exact (analyticAt_pi_iff.mp (hVa z hz) 0).add (analyticAt_pi_iff.mp (hVa z hz) 2)
  · intro j
    fin_cases j
    · exact hprimitives 0
    · exact hprimitives 1
    · exact hprimitives 2
    · exact htrace

end DirichletL
