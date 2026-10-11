import Analysis.PureOriginalMatrix

/-!
The literal initial pure state and its reduced original-coordinate equation.
Source: CDT v2 `defB`, `defB5`, `defB67`, and `diffformulas`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The literal pure initial functions, with their fixed values and primitive constants. -/
noncomputable def pureOriginalState (x : ℂ) : Fin 7 → ℂ :=
  ![1, -Complex.log (1 - x), (-Complex.log (1 - x)) ^ 2, pureDilogarithm x,
    pureB5 (mobiusCoordinate x), pureB6 (mobiusCoordinate x), pureB7 (mobiusCoordinate x)]

theorem analyticAt_pureOriginalState_zero : AnalyticAt ℂ pureOriginalState 0 := by
  have hA := hasFPowerSeriesOnBall_neg_clog_one_sub.hasFPowerSeriesAt.analyticAt
  have hY := analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1)
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact hA
  · exact hA.pow 2
  · exact analyticAt_pureDilogarithm (by norm_num)
  · exact (analyticAt_pureB5 (by norm_num : ‖(0 : ℂ)‖ < 4)).comp_of_eq hY (by simp [mobiusCoordinate])
  · exact (analyticAt_pureB6 (by norm_num : ‖(0 : ℂ)‖ < 4)).comp_of_eq hY (by simp [mobiusCoordinate])
  · exact analyticAt_pureB7.comp_of_eq hY (by simp [mobiusCoordinate])

theorem eventually_hasDerivAt_pureOriginalState : ∀ᶠ x : ℂ in 𝓝[≠] 0,
    HasDerivAt pureOriginalState (pureOriginalMatrix x *ᵥ pureOriginalState x) x := by
  have hsmall : ∀ᶠ x : ℂ in 𝓝 0, ‖x‖ < 1 :=
    continuousAt_id.norm.eventually_lt_const (by norm_num)
  have hslit : ∀ᶠ x in 𝓝 (0 : ℂ), 1 - x ∈ Complex.slitPlane := by
    exact (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
      (Complex.isOpen_slitPlane.mem_nhds (by simp))
  filter_upwards [tendsto_mobiusCoordinate_punctured_zero.eventually
      eventually_hasDerivAt_pureSevenState,
    pureB2_pullback.filter_mono nhdsWithin_le_nhds,
    pureB3_pullback_eq_clog_sq.filter_mono nhdsWithin_le_nhds,
    pureB4_pullback_eq_pureFour.filter_mono nhdsWithin_le_nhds,
    hsmall.filter_mono nhdsWithin_le_nhds, hslit.filter_mono nhdsWithin_le_nhds,
    (eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)).filter_mono nhdsWithin_le_nhds,
    (eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 2)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with x hsys h2 h3 h4 hxsmall hxslit hx1 hx2 hx0
  change x ≠ 0 at hx0
  have hm1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hm2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  have hp1 : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
  have hY : HasDerivAt mobiusCoordinate (x * (x - 2) / (x - 1) ^ 2) x := by
    apply (hasDerivAt_mobiusCoordinate hx1).congr_deriv
    field_simp [hm1, hp1]
    ring
  have hYv := mobiusCoordinate_eq_sq_div hx1
  have hY4 : 4 - mobiusCoordinate x = -(x - 2) ^ 2 / (x - 1) := by
    rw [hYv]
    field_simp [hm1]
    ring
  let A (z : ℂ) := -Complex.log (1 - z)
  have hA : HasDerivAt A (1 / (1 - x)) x := by
    have hd := (((hasDerivAt_const x (1 : ℂ)).sub (hasDerivAt_id x)).clog hxslit).neg
    simpa only [zero_sub, neg_div, neg_neg] using hd
  have hAA : HasDerivAt (fun z => A z ^ 2) (2 * A x / (1 - x)) x := by
    convert hA.pow 2 using 1
    simp
    ring
  have hL : HasDerivAt pureDilogarithm (A x / x) x :=
    (analyticAt_pureDilogarithm hxsmall).differentiableAt.hasDerivAt.congr_deriv
      (deriv_pureDilogarithm hxsmall hx0)
  rw [pureSevenMatrix_mulVec] at hsys
  have h5 : HasDerivAt (fun z => pureB5 (mobiusCoordinate z))
      (A x / (x - 1) + (x - 2) / (2 * x * (x - 1)) * pureB5 (mobiusCoordinate x)) x := by
    apply ((hasDerivAt_pi.mp hsys 4).comp x hY).congr_deriv
    change ((4 * mobiusCoordinate x * 1 - 2 * pureB2 (mobiusCoordinate x) +
      (4 - mobiusCoordinate x) * pureB5 (mobiusCoordinate x)) /
      (2 * (mobiusCoordinate x * (4 - mobiusCoordinate x)))) *
      (x * (x - 2) / (x - 1) ^ 2) = _
    rw [h2, hY4, hYv]
    dsimp only [A, mobiusAnalyticInvolution]
    field_simp [hx0, hm1, hm2]
    ring
  have h6 : HasDerivAt (fun z => pureB6 (mobiusCoordinate z))
      (-(x - 2) / (2 * x * (x - 1)) * A x ^ 2) x := by
    apply ((hasDerivAt_pi.mp hsys 5).comp x hY).congr_deriv
    change (pureB3 (mobiusCoordinate x) / mobiusCoordinate x) *
      (x * (x - 2) / (x - 1) ^ 2) = _
    rw [h3, hYv]
    dsimp only [A]
    field_simp [hx0, hm1]
  have h7 : HasDerivAt (fun z => pureB7 (mobiusCoordinate z))
      ((x - 2) ^ 2 / (x - 1) ^ 2 * (2 * pureDilogarithm x + A x ^ 2 / 2)) x := by
    apply ((hasDerivAt_pi.mp hsys 6).comp x hY).congr_deriv
    change (pureB4 (mobiusCoordinate x) / mobiusCoordinate x) *
      (x * (x - 2) / (x - 1) ^ 2) = _
    rw [h4, hYv]
    dsimp only [A, mobiusAnalyticInvolution]
    field_simp [hx0, hm1]
    ring
  rw [pureOriginalMatrix_mulVec]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const x 1
  · exact hA
  · exact hAA
  · exact hL
  · exact h5
  · exact h6
  · exact h7

end DirichletL
