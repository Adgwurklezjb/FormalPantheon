import Analysis.AnalyticLinearODESections
import Analysis.AnalyticPrimitives

/-!
Normalized actual primitives on an entire prescribed complex ball.
Source: CDT v2 TeX 1739-1744 and 7157-7173. Prior meaning and API review:
-/

namespace DirichletL

open Filter Set
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_analytic_primitive_on_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (Metric.ball c R)) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball c R) ∧ F c = 0 ∧
      ∀ z ∈ Metric.ball c R, HasDerivAt F (f z) z := by
  let A : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun z => !![0, f z; 0, 0]
  have hA : AnalyticOnNhd ℂ A (Metric.ball c R) := by
    intro z hz
    apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j <;> dsimp [A]
    all_goals first | exact hf z hz | exact analyticAt_const
  let D : AnalyticMatrixODE (Fin 2) :=
    ⟨Metric.ball c R, Metric.isOpen_ball, A, hA⟩
  let b : D.domain := ⟨c, Metric.mem_ball_self hR⟩
  letI : ContractibleSpace D.domain :=
    (convex_ball c R).contractibleSpace ⟨c, Metric.mem_ball_self hR⟩
  letI : LocPathConnectedSpace D.domain := Metric.isOpen_ball.locPathConnectedSpace
  obtain ⟨v, hv, hv₀, hvd⟩ := exists_analytic_matrix_ode
    (hA c (Metric.mem_ball_self hR)) ![0, 1]
  obtain ⟨g, hga, hgd, hgv⟩ :=
    D.exists_analytic_solution_of_simplyConnected b v hv hvd
  have hg₀ : g c = ![0, 1] := hgv.self_of_nhds.trans hv₀
  have hg₁ (z : ℂ) (hz : z ∈ Metric.ball c R) :
      HasDerivAt (fun w => g w 1) 0 z := by
    simpa [D, A, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      hasDerivAt_pi.mp (hgd z hz) (1 : Fin 2)
  have hone (z : ℂ) (hz : z ∈ Metric.ball c R) : g z 1 = 1 := by
    have he := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball c R).isPreconnected
      (fun w hw => (hg₁ w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hg₁ w hw).deriv) hz (Metric.mem_ball_self hR)
    simpa [hg₀] using he
  refine ⟨fun z => g z 0, fun z hz => analyticAt_pi_iff.mp (hga z hz) 0, ?_, ?_⟩
  · simp [hg₀]
  · intro z hz
    simpa [D, A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hone z hz] using
      hasDerivAt_pi.mp (hgd z hz) (0 : Fin 2)

end DirichletL
