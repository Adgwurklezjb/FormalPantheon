import Analysis.TwoRadiusHolonomy
import Analysis.ContourHolonomyMargin

/-!
The conditional contradiction in CDT v2, supplied TeX 8384-8404.
-/

namespace DirichletL

open scoped Topology

theorem cdt_two_radius_contour_contradiction (a₀ b₀ c₀ : ℤ)
    (hne : ¬(a₀ = 0 ∧ b₀ = 0 ∧ c₀ = 0)) (ψ : ℂ → ℂ) (P : Fin 14 → ℂ → ℂ)
    (hψ0 : ψ 0 = 0) (hdψ : AnalyticOnNhd ℂ ψ (Metric.closedBall 0 1))
    (hP : ∀ i, P i =ᶠ[𝓝 (0 : ℂ)] fun z => cdtHolonomyFamily a₀ b₀ c₀ i (ψ z))
    (hmero : ∀ i, MeromorphicOn (P i) (Metric.ball 0 1))
    (hderiv : ‖deriv ψ 0‖ = 256 * cdtContourConformalRadius)
    (hJ : twoRadiusMaxIntegral ψ (Real.exp (-1 / 2)) (209 / 1000) ≤ 57 / 5) :
    ¬((a₀ : ℝ) + (b₀ : ℝ) * (lTwoChiMinusThree / 2) +
      (c₀ : ℝ) * (zetaTwo / 4) = 0) := by
  intro hrel
  have hd : deriv ψ 0 ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hderiv]
    have hR := cdtContourConformalRadius_gt_half
    positivity
  have hb := cdt_two_radius_holonomy_bound a₀ b₀ c₀ hrel hne ψ P hψ0 hP hd hdψ hmero
    (r := Real.exp (-1 / 2)) (p := 209 / 1000)
    (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by norm_num)) (by norm_num) (by norm_num)
  rw [hderiv, Real.log_exp] at hb
  have hmargin := cdt_two_radius_margin
  linarith only [hb, hJ, hmargin]

end DirichletL
