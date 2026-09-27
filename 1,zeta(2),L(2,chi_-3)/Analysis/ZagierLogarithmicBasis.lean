import Analysis.ZagierLogarithm

/-!
Local solution coordinates for CDT v2 equation `zagr`. The endpoint
solution has a nonzero logarithmic coefficient near zero, providing
concrete local data for the irreducibility step in Lemma `14functions`.
-/

namespace DirichletL

open Filter Set
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eventuallyEq_zagierSecondOrder_basis {f g h : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hh : AnalyticAt ℂ h z)
    (hz : z * (1 - z) * (1 - 9 * z) ≠ 0)
    (hfode : zagierSecondOrderODE f =ᶠ[𝓝 z] 0)
    (hgode : zagierSecondOrderODE g =ᶠ[𝓝 z] 0)
    (hhode : zagierSecondOrderODE h =ᶠ[𝓝 z] 0)
    (hw : g z * deriv h z - deriv g z * h z ≠ 0) :
    f =ᶠ[𝓝 z] fun w =>
      ((f z * deriv h z - deriv f z * h z) / (g z * deriv h z - deriv g z * h z)) * g w +
        ((g z * deriv f z - deriv g z * f z) / (g z * deriv h z - deriv g z * h z)) * h w := by
  let a := (f z * deriv h z - deriv f z * h z) / (g z * deriv h z - deriv g z * h z)
  let b := (g z * deriv f z - deriv g z * f z) / (g z * deriv h z - deriv g z * h z)
  let F : ℂ → Fin 2 → ℂ := fun w =>
    a • zagierSecondOrderState g w + b • zagierSecondOrderState h w
  have hF : AnalyticAt ℂ F z :=
    ((analyticAt_zagierSecondOrderState hg).const_smul (c := a)).add
      ((analyticAt_zagierSecondOrderState hh).const_smul (c := b))
  have hi : zagierSecondOrderState f z = F z := by
    ext i
    fin_cases i <;> dsimp [F, zagierSecondOrderState, a, b] <;> field_simp [hw]
    · linear_combination -f z * (mul_inv_cancel₀ hw)
    · linear_combination -deriv f z * (mul_inv_cancel₀ hw)
  have hreg : ∀ᶠ w in 𝓝 z, w * (1 - w) * (1 - 9 * w) ≠ 0 :=
    (show ContinuousAt (fun w : ℂ => w * (1 - w) * (1 - 9 * w)) z by fun_prop).eventually_ne hz
  have hfo : ∀ᶠ w in 𝓝 z, HasDerivAt (zagierSecondOrderState f)
      (zagierSecondOrderCompanion w *ᵥ zagierSecondOrderState f w) w := by
    filter_upwards [hf.eventually_analyticAt, hreg, hfode] with w hwf hwr hwo
    exact hasDerivAt_zagierSecondOrderState_of_ode hwf hwr hwo
  have hFo : ∀ᶠ w in 𝓝 z, HasDerivAt F (zagierSecondOrderCompanion w *ᵥ F w) w := by
    filter_upwards [hg.eventually_analyticAt, hh.eventually_analyticAt, hreg, hgode, hhode]
      with w hwg hwh hwr hwog hwoh
    have hsg := hasDerivAt_zagierSecondOrderState_of_ode hwg hwr hwog
    have hsh := hasDerivAt_zagierSecondOrderState_of_ode hwh hwr hwoh
    simpa only [F, Matrix.mulVec_add, Matrix.mulVec_smul] using
      (hsg.const_smul a).add (hsh.const_smul b)
  have he := eventuallyEq_of_analytic_matrix_ode (continuousAt_zagierSecondOrderCompanion hz)
    (analyticAt_zagierSecondOrderState hf) hF hi hfo hFo
  filter_upwards [he] with w hw
  exact congrFun hw (0 : Fin 2)

theorem eventually_zagierEndpointSolution_logarithmic :
    ∀ᶠ x : ℝ in 𝓝 0, 0 < x → ∃ a b : ℂ, b ≠ 0 ∧
      zagierEndpointSolution =ᶠ[𝓝 (x : ℂ)] fun z =>
        a * zagierAnalytic z + b * zagierLogarithmicSolution z := by
  have hnear : ∀ᶠ x : ℝ in 𝓝 0, ∀ᶠ z in 𝓝 (x : ℂ), z ∈ Complex.slitPlane →
      AnalyticAt ℂ zagierLogarithmicSolution z ∧
        zagierSecondOrderODE zagierLogarithmicSolution z = 0 ∧
          zagierWeightedWronskian zagierAnalytic zagierLogarithmicSolution z = 1 := by
    simpa only [Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.eventually
        eventually_zagierLogarithmicSolution.eventually_nhds
  have hupper : ∀ᶠ x : ℝ in 𝓝 0, x < 1 / 9 :=
    continuousAt_id.eventually_lt_const (by norm_num)
  filter_upwards [hnear, hupper] with x hnx hux
  intro hpx
  have hx : x ∈ Ioo 0 (1 / 9 : ℝ) := ⟨hpx, hux⟩
  have hs : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hpx
  obtain ⟨hL, _, hW⟩ := hnx.self_of_nhds hs
  have hnon : (x : ℂ) * (1 - x) * (1 - 9 * x) *
      (zagierAnalytic x * deriv zagierLogarithmicSolution x -
        deriv zagierAnalytic x * zagierLogarithmicSolution x) ≠ 0 := by
    change zagierWeightedWronskian zagierAnalytic zagierLogarithmicSolution x ≠ 0
    rw [hW]
    exact one_ne_zero
  obtain ⟨hreg, hD⟩ := mul_ne_zero_iff.mp hnon
  have hnorm : ‖(x : ℂ)‖ < 1 / 9 := by simpa [abs_of_pos hpx] using hux
  have hx₁ : (x : ℂ) ≠ 1 := by exact_mod_cast (by linarith : x ≠ 1)
  have ht : ‖zagierEndpointCoordinate x‖ < 1 / 9 := by
    rw [zagierEndpointCoordinate_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (zagierEndpointCoordinate_mem_Ioo hx).1]
    exact (zagierEndpointCoordinate_mem_Ioo hx).2
  have hHo : zagierSecondOrderODE zagierAnalytic =ᶠ[𝓝 (x : ℂ)] 0 := by
    filter_upwards [continuous_norm.continuousAt.eventually_lt_const hnorm] with z hz
    exact zagierAnalytic_ode hz
  have hSo : zagierSecondOrderODE zagierEndpointSolution =ᶠ[𝓝 (x : ℂ)] 0 := by
    filter_upwards [eventually_ne_nhds hx₁,
      (analyticAt_zagierEndpointCoordinate hx₁).continuousAt.norm.eventually_lt_const ht]
      with z hz htz
    exact zagierEndpointSolution_ode hz htz
  have hLo : zagierSecondOrderODE zagierLogarithmicSolution =ᶠ[𝓝 (x : ℂ)] 0 := by
    filter_upwards [hnx, Complex.isOpen_slitPlane.mem_nhds hs] with z hz hzs
    exact (hz hzs).2.1
  exact ⟨_, _, div_ne_zero (zagierEndpointSolution_wronskian_ne_zero hx) hD,
    eventuallyEq_zagierSecondOrder_basis (analyticAt_zagierEndpointSolution hx₁ ht)
      (analyticAt_zagierAnalytic hnorm) hL hreg hSo hHo hLo hD⟩

end DirichletL
