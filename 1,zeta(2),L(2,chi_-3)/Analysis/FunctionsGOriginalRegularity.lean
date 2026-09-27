import Analysis.FunctionsGPrimitiveCompanion

/-!
The actual original-coordinate regular locus for the combined H state.
Source: CDT v2 `defH`, `defG`, and `14functions`, TeX 7751-7771,
7861-7872, and 8044-8074. Prior meanings and edge checks:
-/

namespace DirichletL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_mobiusAnalyticInvolution_lt_one {x : ℂ} (hx : ‖x‖ < 1 / 2) :
    ‖mobiusAnalyticInvolution x‖ < 1 := by
  have hlow : 1 - ‖x‖ ≤ ‖x - 1‖ := by
    simpa only [norm_one, norm_sub_rev (1 : ℂ) x] using norm_sub_norm_le (1 : ℂ) x
  have hden : 0 < ‖x - 1‖ := by linarith
  change ‖x / (x - 1)‖ < 1
  rw [norm_div]
  apply (div_lt_iff₀ hden).mpr
  linarith

theorem mobiusAnalyticInvolution_mem_hForcedRegularSet_of_ne {x : ℂ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx8 : x ≠ -1 / 8) :
    mobiusAnalyticInvolution x ∈ hForcedRegularSet := by
  apply (mem_hForcedRegularSet_iff _).mpr
  refine ⟨div_ne_zero hx0 (sub_ne_zero.mpr hx1), ?_,
    mobiusAnalyticInvolution_ne_one hx1⟩
  intro he
  have h := (div_eq_iff (sub_ne_zero.mpr hx1)).mp he
  apply hx8
  linear_combination (9 / 8 : ℂ) * h

theorem analyticAt_gPrimitiveMatrix_of_ne (b c k0 k1 : ℂ) {x : ℂ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx9 : x ≠ 1 / 9) (hx8 : x ≠ -1 / 8) :
    AnalyticAt ℂ (gPrimitiveMatrix b c k0 k1) x := by
  have hi := analyticAt_mobiusAnalyticInvolution hx1
  have hY := analyticAt_mobiusCoordinate hx1
  have hdi := hi.deriv
  have hdY := hY.deriv
  have hY0 := mobiusCoordinate_ne_zero hx0 hx1
  have hY2 := pow_ne_zero 2 hY0
  have hF := analyticOnNhd_hForcedMatrix x
    ((mem_hForcedRegularSet_iff x).mpr ⟨hx0, hx9, hx1⟩)
  have hFi := (analyticOnNhd_hForcedMatrix (mobiusAnalyticInvolution x)
    (mobiusAnalyticInvolution_mem_hForcedRegularSet_of_ne hx0 hx1 hx8)).comp hi
  have hFj (j : Fin 4) := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hF 1) j
  have hFij (j : Fin 4) := analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hFi 1) j
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [gPrimitiveMatrix, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    fun_prop (disch := assumption)

end DirichletL
