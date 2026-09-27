import Analysis.AnalyticLinearODE
import Analysis.ZagierEndpointSymmetry

/-!
Regular initial states for CDT v2 equation `zagr`, used for the
irreducibility assertion in Lemma `14functions`. The two actual endpoint
solutions have a nonzero Wronskian on the real interval `(0, 1/9)`.
-/

namespace DirichletL

open Filter Set
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The value and ordinary first derivative of a scalar solution. -/
noncomputable def zagierSecondOrderState (f : ℂ → ℂ) (z : ℂ) : Fin 2 → ℂ :=
  ![f z, deriv f z]

/-- The regular companion matrix of CDT's second-order equation. -/
noncomputable def zagierSecondOrderCompanion (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -(9 * z - 3) / (z * (1 - z) * (1 - 9 * z)),
    -(1 - 20 * z + 27 * z ^ 2) / (z * (1 - z) * (1 - 9 * z))]

theorem analyticAt_zagierSecondOrderState {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) : AnalyticAt ℂ (zagierSecondOrderState f) z := by
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact hf
  · exact hf.deriv

theorem continuousAt_zagierSecondOrderCompanion {z : ℂ}
    (hz : z * (1 - z) * (1 - 9 * z) ≠ 0) :
    ContinuousAt zagierSecondOrderCompanion z := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [zagierSecondOrderCompanion] <;>
    fun_prop (disch := assumption)

theorem hasDerivAt_zagierSecondOrderState_of_ode {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : z * (1 - z) * (1 - 9 * z) ≠ 0)
    (hode : zagierSecondOrderODE f z = 0) :
    HasDerivAt (zagierSecondOrderState f)
      (zagierSecondOrderCompanion z *ᵥ zagierSecondOrderState f z) z := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [zagierSecondOrderState, zagierSecondOrderCompanion, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] using hf.differentiableAt.hasDerivAt
  · have h := hf.deriv.differentiableAt.hasDerivAt
    convert h using 1
    dsimp [zagierSecondOrderState, zagierSecondOrderCompanion, Matrix.mulVec, dotProduct]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    dsimp [zagierSecondOrderODE] at hode
    simp only [mul_ne_zero_iff] at hz
    field_simp [hz.1.1, hz.1.2, hz.2]
    linear_combination -hode

theorem eq_zero_germ_of_zagierSecondOrder_initial_relation {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z)
    (hz : z * (1 - z) * (1 - 9 * z) ≠ 0)
    (hfode : zagierSecondOrderODE f =ᶠ[𝓝 z] 0)
    (hgode : zagierSecondOrderODE g =ᶠ[𝓝 z] 0) {a b : ℂ}
    (h₀ : a * f z + b * g z = 0) (h₁ : a * deriv f z + b * deriv g z = 0) :
    (fun w => a * f w + b * g w) =ᶠ[𝓝 z] 0 := by
  let F : ℂ → Fin 2 → ℂ := fun w =>
    a • zagierSecondOrderState f w + b • zagierSecondOrderState g w
  have hF : AnalyticAt ℂ F z :=
    ((analyticAt_zagierSecondOrderState hf).const_smul (c := a)).add
      ((analyticAt_zagierSecondOrderState hg).const_smul (c := b))
  have hinit : F z = 0 := by
    ext i
    fin_cases i
    · exact h₀
    · exact h₁
  have hreg : ∀ᶠ w in 𝓝 z, w * (1 - w) * (1 - 9 * w) ≠ 0 :=
    (show ContinuousAt (fun w : ℂ => w * (1 - w) * (1 - 9 * w)) z by fun_prop).eventually_ne hz
  have he := eventuallyEq_zero_of_analytic_matrix_ode
    (continuousAt_zagierSecondOrderCompanion hz) hF hinit (by
      filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt,
        hfode, hgode, hreg] with w hwf hwg hwof hwog hw
      have hsf := hasDerivAt_zagierSecondOrderState_of_ode hwf hw hwof
      have hsg := hasDerivAt_zagierSecondOrderState_of_ode hwg hw hwog
      simpa only [F, Matrix.mulVec_add, Matrix.mulVec_smul] using
        (hsf.const_smul a).add (hsg.const_smul b))
  filter_upwards [he] with w hw
  exact congrFun hw (0 : Fin 2)

theorem zagierEndpointSolution_wronskian_ne_zero {x : ℝ} (hx : x ∈ Ioo 0 (1 / 9 : ℝ)) :
    zagierAnalytic x * deriv zagierEndpointSolution x -
      deriv zagierAnalytic x * zagierEndpointSolution x ≠ 0 := by
  have hnorm : ‖(x : ℂ)‖ < 1 / 9 := by simpa [abs_of_pos hx.1] using hx.2
  have hx₁ : (x : ℂ) ≠ 1 := by exact_mod_cast (by linarith [hx.2] : x ≠ 1)
  have ht : ‖zagierEndpointCoordinate x‖ < 1 / 9 := by
    rw [zagierEndpointCoordinate_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (zagierEndpointCoordinate_mem_Ioo hx).1]
    exact (zagierEndpointCoordinate_mem_Ioo hx).2
  have ha := analyticAt_zagierAnalytic hnorm
  have hb := analyticAt_zagierEndpointSolution hx₁ ht
  have hreg : (x : ℂ) * (1 - x) * (1 - 9 * x) ≠ 0 := by
    have h₁ : 0 < 1 - x := by linarith [hx.2]
    have h₉ : 0 < 1 - 9 * x := by linarith [hx.2]
    have hreal : x * (1 - x) * (1 - 9 * x) ≠ 0 :=
      ne_of_gt (mul_pos (mul_pos hx.1 h₁) h₉)
    exact_mod_cast hreal
  have hao : zagierSecondOrderODE zagierAnalytic =ᶠ[𝓝 (x : ℂ)] 0 := by
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hnorm] with z hz
    exact zagierAnalytic_ode hz
  have hbo : zagierSecondOrderODE zagierEndpointSolution =ᶠ[𝓝 (x : ℂ)] 0 := by
    filter_upwards [eventually_ne_nhds hx₁,
      (analyticAt_zagierEndpointCoordinate hx₁).continuousAt.norm.eventually_lt_const ht]
      with z hz htz
    exact zagierEndpointSolution_ode hz htz
  intro hw
  have he := eq_zero_germ_of_zagierSecondOrder_initial_relation ha hb hreg hao hbo
    (a := zagierEndpointSolution x) (b := -zagierAnalytic x) (by ring) (by
      linear_combination -hw)
  have hzero := (eq_zero_of_zagierEndpointSolution_relation hx he).1
  have hp := zagierEndpointSolution_ofReal_re_pos hx
  simp [hzero] at hp

end DirichletL
