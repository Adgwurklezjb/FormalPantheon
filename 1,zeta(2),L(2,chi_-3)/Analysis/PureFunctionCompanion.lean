import Analysis.AnalyticLinearODEGerms
import Analysis.PureFunctionSevenIndependence

/-!
The literal pure-seven vector as an analytic matrix system on C minus {0,4}.
Source: CDT v2, `defB`, `defB5`, `defB67`, and `diffformulas`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The regular domain of the pure-seven differential system. -/
def pureRegularSet : Set ℂ := {z | z * (4 - z) ≠ 0}

theorem isOpen_pureRegularSet : IsOpen pureRegularSet :=
  isOpen_ne_fun (by fun_prop) continuous_const

theorem mem_pureRegularSet_iff (z : ℂ) : z ∈ pureRegularSet ↔ z ≠ 0 ∧ z ≠ 4 := by
  change z * (4 - z) ≠ 0 ↔ _
  rw [mul_ne_zero_iff, sub_ne_zero, ne_comm (a := (4 : ℂ))]

/-- The homogeneous matrix for (1,B2,B3,B4,B5,B6,B7). -/
noncomputable def pureSevenMatrix (z : ℂ) : Matrix (Fin 7) (Fin 7) ℂ :=
  !![0, 0, 0, 0, 0, 0, 0;
    z ^ 2 / (z * (4 - z)), (2 - z) / (z * (4 - z)), 0, 0, 0, 0, 0;
    2 * z / (z * (4 - z)), -1 / (z * (4 - z)), 0, 0, 0, 0, 0;
    -2, (4 - z) / (z * (4 - z)), 0, (2 - z) / (z * (4 - z)), 0, 0, 0;
    2 * z / (z * (4 - z)), -1 / (z * (4 - z)), 0, 0,
      (4 - z) / (2 * (z * (4 - z))), 0, 0;
    0, 0, 1 / z, 0, 0, 0, 0;
    0, 0, 0, 1 / z, 0, 0, 0]

theorem pureSevenMatrix_mulVec (z : ℂ) (v : Fin 7 → ℂ) :
    pureSevenMatrix z *ᵥ v =
      ![0, (z ^ 2 * v 0 + (2 - z) * v 1) / (z * (4 - z)),
        (2 * z * v 0 - v 1) / (z * (4 - z)),
        -2 * v 0 + ((4 - z) * v 1 + (2 - z) * v 3) / (z * (4 - z)),
        (4 * z * v 0 - 2 * v 1 + (4 - z) * v 4) / (2 * (z * (4 - z))),
        v 2 / z, v 3 / z] := by
  ext i
  fin_cases i <;> simp [pureSevenMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    div_eq_mul_inv, mul_inv_rev] <;> ring

theorem analyticOnNhd_pureSevenMatrix : AnalyticOnNhd ℂ pureSevenMatrix pureRegularSet := by
  intro z hz
  have hz0 := ((mem_pureRegularSet_iff z).mp hz).1
  have hp : z * (4 - z) ≠ 0 := hz
  have h2p : 2 * (z * (4 - z)) ≠ 0 := mul_ne_zero (by norm_num) hp
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [pureSevenMatrix, Matrix.of_apply, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    fun_prop (disch := assumption)

/-- The proved analytic matrix data for the literal pure-seven family. -/
noncomputable def pureSevenSystem : AnalyticMatrixODE (Fin 7) where
  domain := pureRegularSet
  isOpen_domain := isOpen_pureRegularSet
  matrix := pureSevenMatrix
  analytic := analyticOnNhd_pureSevenMatrix

/-- The existing pure functions, transposed into a vector-valued analytic function. -/
noncomputable def pureSevenState (z : ℂ) : Fin 7 → ℂ :=
  ![1, pureB2 z, pureB3 z, pureB4 z, pureB5 z, pureB6 z, pureB7 z]

theorem pureSevenState_apply (z : ℂ) (i : Fin 7) :
    pureSevenState z i = pureSevenDescentFamily i z := by
  fin_cases i <;> rfl

theorem analyticAt_pureSevenState_zero : AnalyticAt ℂ pureSevenState 0 := by
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact analyticAt_pureB2 (by norm_num)
  · exact analyticAt_pureB3 (by norm_num)
  · exact analyticAt_pureB4
  · exact analyticAt_pureB5 (by norm_num)
  · exact analyticAt_pureB6 (by norm_num)
  · exact analyticAt_pureB7

theorem eventually_hasDerivAt_pureSevenState : ∀ᶠ z : ℂ in 𝓝[≠] 0,
    HasDerivAt pureSevenState (pureSevenMatrix z *ᵥ pureSevenState z) z := by
  have hn4 := eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 4)
  filter_upwards [analyticAt_pureSevenState_zero.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    pureB2_ode.filter_mono nhdsWithin_le_nhds, pureB3_ode.filter_mono nhdsWithin_le_nhds,
    pureB4_ode.filter_mono nhdsWithin_le_nhds, pureB5_ode.filter_mono nhdsWithin_le_nhds,
    pureB6_deriv, pureB7_deriv, hn4.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with z ha h2 h3 h4 h5 h6 h7 hz4 hz0
  change z ≠ 0 at hz0
  have hp : z * (4 - z) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr hz4.symm)
  rw [pureSevenMatrix_mulVec]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const z 1
  · apply ((analyticAt_pi_iff.mp ha 1).differentiableAt.hasDerivAt).congr_deriv
    change deriv pureB2 z = (z ^ 2 * 1 + (2 - z) * pureB2 z) / (z * (4 - z))
    apply (eq_div_iff hp).mpr
    linear_combination h2
  · apply ((analyticAt_pi_iff.mp ha 2).differentiableAt.hasDerivAt).congr_deriv
    change deriv pureB3 z = (2 * z * 1 - pureB2 z) / (z * (4 - z))
    apply (eq_div_iff hp).mpr
    linear_combination h3
  · apply ((analyticAt_pi_iff.mp ha 3).differentiableAt.hasDerivAt).congr_deriv
    change deriv pureB4 z = -2 * 1 +
      ((4 - z) * pureB2 z + (2 - z) * pureB4 z) / (z * (4 - z))
    field_simp [hz0, sub_ne_zero.mpr hz4.symm]
    linear_combination h4
  · apply ((analyticAt_pi_iff.mp ha 4).differentiableAt.hasDerivAt).congr_deriv
    change deriv pureB5 z =
      (4 * z * 1 - 2 * pureB2 z + (4 - z) * pureB5 z) / (2 * (z * (4 - z)))
    apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hp)).mpr
    linear_combination h5
  · exact ((analyticAt_pi_iff.mp ha 5).differentiableAt.hasDerivAt).congr_deriv h6
  · exact ((analyticAt_pi_iff.mp ha 6).differentiableAt.hasDerivAt).congr_deriv h7

theorem exists_pureSeven_initial_radius :
    ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, ‖z‖ < R → AnalyticAt ℂ pureSevenState z ∧
      (z ≠ 0 → z ∈ pureRegularSet ∧
        ∀ᶠ w in 𝓝 z, HasDerivAt pureSevenState (pureSevenMatrix w *ᵥ pureSevenState w) w) := by
  have ho : ∀ᶠ z : ℂ in 𝓝 0, z ≠ 0 →
      HasDerivAt pureSevenState (pureSevenMatrix z *ᵥ pureSevenState z) z :=
    eventually_nhdsWithin_iff.mp eventually_hasDerivAt_pureSevenState
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (analyticAt_pureSevenState_zero.eventually_analyticAt.and
      (ho.eventually_nhds.and (eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 4))))
  refine ⟨R, hR, ?_⟩
  intro z hz
  obtain ⟨ha, ho, hz4⟩ := hball (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  refine ⟨ha, fun hz0 => ⟨(mem_pureRegularSet_iff z).mpr ⟨hz0, hz4⟩, ?_⟩⟩
  filter_upwards [ho, eventually_ne_nhds hz0] with w hw hw0
  exact hw hw0

end DirichletL
