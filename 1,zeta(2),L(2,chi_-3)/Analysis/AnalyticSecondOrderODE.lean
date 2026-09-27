import Analysis.AnalyticLinearODE
import Analysis.AnalyticLinearODEExistence

/-!
Regular scalar second-order analytic equations, via the verified matrix ODE API.
These supply both summands in the pullback decomposition for CDT v2, `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The standard companion matrix for `a f'' + b f' + c f = 0`. -/
noncomputable def analyticSecondOrderCompanion (a b c : ℂ → ℂ) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -c z / a z, -b z / a z]

theorem analyticAt_analyticSecondOrderCompanion {a b c : ℂ → ℂ} {z : ℂ}
    (ha : AnalyticAt ℂ a z) (hb : AnalyticAt ℂ b z) (hc : AnalyticAt ℂ c z)
    (hreg : a z ≠ 0) : AnalyticAt ℂ (analyticSecondOrderCompanion a b c) z := by
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact analyticAt_const
  · exact analyticAt_const
  · exact hc.neg.div ha hreg
  · exact hb.neg.div ha hreg

theorem exists_analytic_secondOrder_ode {a b c : ℂ → ℂ} {z0 : ℂ}
    (ha : AnalyticAt ℂ a z0) (hb : AnalyticAt ℂ b z0) (hc : AnalyticAt ℂ c z0)
    (hreg : a z0 ≠ 0) (u v : ℂ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f z0 ∧ f z0 = u ∧ deriv f z0 = v ∧
      (fun z => a z * deriv (deriv f) z + b z * deriv f z + c z * f z) =ᶠ[𝓝 z0] 0 := by
  obtain ⟨V, hV, hinit, hode⟩ := exists_analytic_matrix_ode
    (analyticAt_analyticSecondOrderCompanion ha hb hc hreg) ![u, v]
  have hd : deriv (fun z => V z 0) =ᶠ[𝓝 z0] fun z => V z 1 := by
    filter_upwards [hode] with z hz
    simpa [analyticSecondOrderCompanion, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using
      (hasDerivAt_pi.mp hz 0).deriv
  refine ⟨fun z => V z 0, analyticAt_pi_iff.mp hV 0, congrFun hinit 0,
    hd.self_of_nhds.trans (congrFun hinit 1), ?_⟩
  filter_upwards [hode, hd, hd.deriv, ha.continuousAt.eventually_ne hreg]
    with z hz hd₁ hd₂ haz
  have hs := (hasDerivAt_pi.mp hz 1).deriv
  simp only [analyticSecondOrderCompanion, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_fin_one] at hs
  change a z * deriv (deriv (fun w => V w 0)) z + b z * deriv (fun w => V w 0) z +
    c z * V z 0 = 0
  rw [hd₂, hs, hd₁]
  field_simp [haz] <;> ring

theorem eventuallyEq_zero_of_analytic_secondOrder_ode {a b c f : ℂ → ℂ} {z0 : ℂ}
    (ha : AnalyticAt ℂ a z0) (hb : AnalyticAt ℂ b z0) (hc : AnalyticAt ℂ c z0)
    (hreg : a z0 ≠ 0) (hf : AnalyticAt ℂ f z0) (h₀ : f z0 = 0) (h₁ : deriv f z0 = 0)
    (hode : (fun z => a z * deriv (deriv f) z + b z * deriv f z + c z * f z) =ᶠ[𝓝 z0] 0) :
    f =ᶠ[𝓝 z0] 0 := by
  let V : ℂ → Fin 2 → ℂ := fun z => ![f z, deriv f z]
  have hV : AnalyticAt ℂ V z0 := by
    apply analyticAt_pi_iff.mpr
    intro i
    fin_cases i
    · exact hf
    · exact hf.deriv
  have hinit : V z0 = 0 := by simp [V, h₀, h₁]
  have hVo : ∀ᶠ z in 𝓝 z0,
      HasDerivAt V (analyticSecondOrderCompanion a b c z *ᵥ V z) z := by
    filter_upwards [hf.eventually_analyticAt, hode, ha.continuousAt.eventually_ne hreg]
      with z hfz ho haz
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [V, analyticSecondOrderCompanion, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        using hfz.differentiableAt.hasDerivAt
    · convert hfz.deriv.differentiableAt.hasDerivAt using 1
      dsimp [V, analyticSecondOrderCompanion, Matrix.mulVec, dotProduct]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      field_simp [haz]
      change a z * deriv (deriv f) z + b z * deriv f z + c z * f z = 0 at ho
      linear_combination -ho
  have he := eventuallyEq_zero_of_analytic_matrix_ode
    (analyticAt_analyticSecondOrderCompanion ha hb hc hreg).continuousAt hV hinit hVo
  filter_upwards [he] with z hz
  exact congrFun hz (0 : Fin 2)

end DirichletL
