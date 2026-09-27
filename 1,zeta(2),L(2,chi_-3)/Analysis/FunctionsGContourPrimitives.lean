import Analysis.FunctionsGContourDoublePullback
import Analysis.AnalyticSquareDescent

/-!
G and its three normalized primitives on the ordinary contour parameter disc.
Source: CDT v2 `14functions`, TeX 8044-8051.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem exists_analytic_cdtContour_gPrimitive_pullback (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ F : Fin 4 → ℂ → ℂ,
      (∀ j, AnalyticOnNhd ℂ (F j) (Metric.ball 0 1)) ∧
      ∀ j, F j =ᶠ[𝓝 (0 : ℂ)] fun z =>
        zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
          (j.castAdd 3) (cdtContourMap z) := by
  classical
  obtain ⟨F, hFa, hFg⟩ := exists_analytic_cdtContour_gPrimitive_double_pullback a b c hrel
  obtain ⟨R, hR, hinit⟩ := exists_gPrimitives_initial_radius a b c hrel
  have hg (j : Fin 4) : AnalyticAt ℂ
      (fun z => zagierAuxiliaryFunctions (symmetrizedDescent (a • hA + b • hB + c • hC))
        (j.castAdd 3) (cdtContourMap z)) 0 := by
    have hj := (hinit 0 (by simpa only [norm_zero] using hR)).2.2.1 (j.castAdd 3)
    rw [mobiusCoordinate_zero] at hj
    exact hj.comp_of_eq (analyticOnNhd_cdtContourMap 0 (by simp)) cdtContourMap_zero
  choose G hG using fun j : Fin 4 =>
    exists_analytic_square_descent_on_unit_ball (hFa j) (hg j) (hFg j)
  exact ⟨G, fun j => (hG j).1, fun j => (hG j).2.1⟩

end DirichletL
