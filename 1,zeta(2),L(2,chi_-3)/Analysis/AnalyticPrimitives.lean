import Analysis.AnalyticLinearODEExistence

/-!
Local analytic primitives used for the logarithmic solutions of CDT v2
equation `zagr`, supporting the irreducibility step in Lemma `14functions`.
-/

namespace DirichletL

open Filter Set
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eventuallyEq_const_of_eventually_hasDerivAt_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : ∀ᶠ z in 𝓝 z₀, HasDerivAt f 0 z) :
    f =ᶠ[𝓝 z₀] fun _ => f z₀ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hf
  filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
  exact Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball z₀ r).isPreconnected
    (fun w hw => (hball hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (hball hw).deriv) hz (Metric.mem_ball_self hr)

theorem exists_analytic_primitive {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    ∃ B : ℂ → ℂ, AnalyticAt ℂ B z₀ ∧ B z₀ = 0 ∧
      ∀ᶠ z in 𝓝 z₀, HasDerivAt B (f z) z := by
  let A : ℂ → Matrix (Fin 2) (Fin 2) ℂ := fun z => !![0, f z; 0, 0]
  have hA : AnalyticAt ℂ A z₀ := by
    apply analyticAt_pi_iff.mpr
    intro i
    apply analyticAt_pi_iff.mpr
    intro j
    fin_cases i <;> fin_cases j <;> dsimp [A]
    all_goals first | exact hf | exact analyticAt_const
  obtain ⟨v, hv, hv₀, hvd⟩ := exists_analytic_matrix_ode hA ![0, 1]
  have hv₁ : ∀ᶠ z in 𝓝 z₀, HasDerivAt (fun w => v w 1) 0 z := by
    filter_upwards [hvd] with z hz
    simpa [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      hasDerivAt_pi.mp hz (1 : Fin 2)
  have he := eventuallyEq_const_of_eventually_hasDerivAt_zero hv₁
  refine ⟨fun z => v z 0, analyticAt_pi_iff.mp hv 0, ?_, ?_⟩
  · simp only [hv₀, Matrix.cons_val_zero]
  · filter_upwards [hvd, he] with z hz hez
    simpa [A, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hez, hv₀] using
      hasDerivAt_pi.mp hz (0 : Fin 2)

end DirichletL
