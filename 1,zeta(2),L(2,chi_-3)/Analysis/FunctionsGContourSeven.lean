import Analysis.FunctionsGContourPrimitives
import Analysis.MeromorphicPullbackDerivatives

/-!
The actual seven G functions on CDT's contour parameter disc.
Source: CDT v2 `14functions`, TeX 8044-8051.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem exists_meromorphic_cdtContour_zagier_pullback (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ F : Fin 7 → ℂ → ℂ,
      (∀ j, MeromorphicOn (F j) (Metric.ball 0 1)) ∧
      ∀ j, F j =ᶠ[𝓝 (0 : ℂ)] fun z =>
        zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
          j (cdtContourMap z) := by
  obtain ⟨F, hFa, hFg⟩ := exists_analytic_cdtContour_gPrimitive_pullback a b c hrel
  let G := gLinearCombinationAnalytic a b c
  have hφ (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : AnalyticAt ℂ cdtContourMap z :=
    analyticOnNhd_cdtContourMap z (Metric.ball_subset_closedBall hz)
  have hφ0 := hφ 0 (by simp)
  have hφd : deriv cdtContourMap 0 ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_deriv_cdtContourMap_zero]
    have hr := cdtContourConformalRadius_gt_half
    positivity
  have hG : AnalyticAt ℂ G (cdtContourMap 0) := by
    simpa only [G, cdtContourMap_zero] using analyticAt_gLinearCombinationAnalytic_zero a b c hrel
  have he0 : F 3 =ᶠ[𝓝 (0 : ℂ)] fun z => G (cdtContourMap z) := hFg 3
  let D1 (z : ℂ) := deriv (F 3) z / deriv cdtContourMap z
  let D2 (z : ℂ) := deriv D1 z / deriv cdtContourMap z
  let D3 (z : ℂ) := deriv D2 z / deriv cdtContourMap z
  have hm1 : MeromorphicOn D1 (Metric.ball 0 1) := fun z hz =>
    (meromorphicAt_deriv (hFa 3 z hz).meromorphicAt).div' (hφ z hz).deriv.meromorphicAt
  have hm2 : MeromorphicOn D2 (Metric.ball 0 1) := fun z hz =>
    (meromorphicAt_deriv (hm1 z hz)).div' (hφ z hz).deriv.meromorphicAt
  have hm3 : MeromorphicOn D3 (Metric.ball 0 1) := fun z hz =>
    (meromorphicAt_deriv (hm2 z hz)).div' (hφ z hz).deriv.meromorphicAt
  have he1 : D1 =ᶠ[𝓝 (0 : ℂ)] fun z => deriv G (cdtContourMap z) :=
    eventuallyEq_deriv_div_of_eventuallyEq_comp hG hφ0 hφd he0
  have he2 : D2 =ᶠ[𝓝 (0 : ℂ)] fun z => deriv (deriv G) (cdtContourMap z) :=
    eventuallyEq_deriv_div_of_eventuallyEq_comp hG.deriv hφ0 hφd he1
  have he3 : D3 =ᶠ[𝓝 (0 : ℂ)] fun z => deriv (deriv (deriv G)) (cdtContourMap z) :=
    eventuallyEq_deriv_div_of_eventuallyEq_comp hG.deriv.deriv hφ0 hφd he2
  let P : Fin 7 → ℂ → ℂ := ![F 0, F 1, F 2, F 3, D1, D2, D3]
  refine ⟨P, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact (hFa 0).meromorphicOn
    · exact (hFa 1).meromorphicOn
    · exact (hFa 2).meromorphicOn
    · exact (hFa 3).meromorphicOn
    · exact hm1
    · exact hm2
    · exact hm3
  · intro j
    fin_cases j
    · exact hFg 0
    · exact hFg 1
    · exact hFg 2
    · exact hFg 3
    · exact he1
    · exact he2
    · exact he3

end DirichletL
