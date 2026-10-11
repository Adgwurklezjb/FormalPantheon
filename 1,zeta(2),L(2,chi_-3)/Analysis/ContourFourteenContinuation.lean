import Analysis.FunctionsGContourSeven
import Analysis.PureContourSeven
import Analysis.HolonomyFamily
import Analysis.TwoRadiusContradiction

/-!
Actual fourteen-function continuation along the concrete CDT contour.
Source: CDT v2 `14functions`, `typesA`, and TeX 8384-8404.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem exists_meromorphic_cdtContour_holonomy_pullback (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) :
    ∃ F : Fin 14 → ℂ → ℂ,
      (∀ i, MeromorphicOn (F i) (Metric.ball 0 1)) ∧
      ∀ i, F i =ᶠ[𝓝 (0 : ℂ)] fun z => cdtHolonomyFamily a b c i (cdtContourMap z) := by
  obtain ⟨G, hGm, hGg⟩ := exists_meromorphic_cdtContour_zagier_pullback a b c hrel
  obtain ⟨B, hBa, hBg⟩ := exists_analytic_cdtContour_pure_pullback
  let P : Fin 14 → ℂ → ℂ := Fin.append G B
  have hPm (i : Fin 14) : MeromorphicOn (P i) (Metric.ball 0 1) := by
    refine Fin.addCases (m := 7) (n := 7) ?_ ?_ i
    · intro j
      simpa only [P, Fin.append_left] using hGm j
    · intro j
      simpa only [P, Fin.append_right] using (hBa j).meromorphicOn
  have hPg (i : Fin 14) : P i =ᶠ[𝓝 (0 : ℂ)] fun z =>
      cdtFourteenFamily a b c i (cdtContourMap z) := by
    refine Fin.addCases (m := 7) (n := 7) ?_ ?_ i
    · intro j
      simpa only [P, cdtFourteenFamily, Fin.append_left] using hGg j
    · intro j
      simpa only [P, cdtFourteenFamily, Fin.append_right] using hBg j
  exact ⟨fun i => P (cdtHolonomyOrder i), fun i => hPm (cdtHolonomyOrder i),
    fun i => hPg (cdtHolonomyOrder i)⟩

theorem cdt_contour_no_integer_relation_of_integral_bound
    (hJ : twoRadiusMaxIntegral cdtContourMap (Real.exp (-1 / 2)) (209 / 1000) ≤ 57 / 5)
    (a b c : ℤ) (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    ¬((a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0) := by
  intro hrel
  have hrelQ : ((a : ℚ) : ℝ) + ((b : ℚ) : ℝ) * (lTwoChiMinusThree / 2) +
      ((c : ℚ) : ℝ) * (zetaTwo / 4) = 0 := by
    simpa only [Rat.cast_intCast] using hrel
  obtain ⟨P, hPm, hPg⟩ := exists_meromorphic_cdtContour_holonomy_pullback a b c hrelQ
  exact cdt_two_radius_contour_contradiction a b c hne cdtContourMap P cdtContourMap_zero
    analyticOnNhd_cdtContourMap hPg hPm norm_deriv_cdtContourMap_zero hJ hrel

end DirichletL
