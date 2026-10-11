import Analysis.ZagierDescentAnalyticODE
import Analysis.ZagierSingularities

/-!
The companion first-order system of CDT v2 equation `explicitode`, on the
nonsingular locus of its displayed polynomial coefficients.
-/

namespace DirichletL

open scoped Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The nonsingular locus of the displayed fourth-order scalar equation. -/
def zagierODERegularSet : Set ℂ := {z | (zagierODECoeff 4).eval z ≠ 0}

theorem isOpen_zagierODERegularSet : IsOpen zagierODERegularSet :=
  isOpen_ne_fun (zagierODECoeff 4).continuous continuous_const

theorem mem_zagierODERegularSet_iff (z : ℂ) :
    z ∈ zagierODERegularSet ↔
      z ≠ 0 ∧ z ≠ 4 ∧ z ≠ -1 / 72 ∧ zagierSingularCubic.eval z ≠ 0 := by
  simp only [zagierODERegularSet, Set.mem_setOf_eq, ne_eq,
    eval_zagierODECoeff_four_eq_zero_iff, not_or]

/-- The function and its first three derivatives, in scalar ODE order. -/
noncomputable def zagierODEState (f : ℂ → ℂ) (z : ℂ) : Fin 4 → ℂ :=
  ![f z, deriv f z, deriv (deriv f) z, deriv (deriv (deriv f)) z]

/-- The companion matrix, used only at regular points in the ODE theorems. -/
noncomputable def zagierODECompanion (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1;
     -(zagierODECoeff 0).eval z / (zagierODECoeff 4).eval z,
     -(zagierODECoeff 1).eval z / (zagierODECoeff 4).eval z,
     -(zagierODECoeff 2).eval z / (zagierODECoeff 4).eval z,
     -(zagierODECoeff 3).eval z / (zagierODECoeff 4).eval z]

theorem zagierODECompanion_mulVec (z : ℂ) (v : Fin 4 → ℂ) :
    zagierODECompanion z *ᵥ v =
      ![v 1, v 2, v 3,
        -((zagierODECoeff 0).eval z * v 0 + (zagierODECoeff 1).eval z * v 1 +
          (zagierODECoeff 2).eval z * v 2 + (zagierODECoeff 3).eval z * v 3) /
            (zagierODECoeff 4).eval z] := by
  ext i
  fin_cases i <;> simp [zagierODECompanion, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    div_eq_mul_inv]
  ring

theorem analyticOnNhd_zagierODEState {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) : AnalyticOnNhd ℂ (zagierODEState f) U := by
  apply analyticOnNhd_pi_iff.mpr
  intro i
  fin_cases i
  · exact hf
  · exact hf.deriv
  · exact hf.deriv.deriv
  · exact hf.deriv.deriv.deriv

theorem analyticOnNhd_zagierODECompanion :
    AnalyticOnNhd ℂ zagierODECompanion zagierODERegularSet := by
  have hc (i : Fin 5) : AnalyticOnNhd ℂ (fun z => (zagierODECoeff i).eval z)
      zagierODERegularSet :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (zagierODECoeff i)).mono (Set.subset_univ _)
  have hn (z : ℂ) (hz : z ∈ zagierODERegularSet) : (zagierODECoeff 4).eval z ≠ 0 := hz
  apply analyticOnNhd_pi_iff.mpr
  intro i
  apply analyticOnNhd_pi_iff.mpr
  intro j
  fin_cases i
  · fin_cases j <;> exact analyticOnNhd_const
  · fin_cases j <;> exact analyticOnNhd_const
  · fin_cases j <;> exact analyticOnNhd_const
  · fin_cases j
    · exact (hc 0).neg.div (hc 4) hn
    · exact (hc 1).neg.div (hc 4) hn
    · exact (hc 2).neg.div (hc 4) hn
    · exact (hc 3).neg.div (hc 4) hn

theorem hasDerivAt_zagierODEState {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    HasDerivAt (zagierODEState f)
      ![deriv f z, deriv (deriv f) z, deriv (deriv (deriv f)) z,
        deriv (deriv (deriv (deriv f))) z] z := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hf.differentiableAt.hasDerivAt
  · exact hf.deriv.differentiableAt.hasDerivAt
  · exact hf.deriv.deriv.differentiableAt.hasDerivAt
  · exact hf.deriv.deriv.deriv.differentiableAt.hasDerivAt

/-- The fourth-order equation is the companion system at every regular point. -/
theorem hasDerivAt_zagierODEState_of_ode {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : z ∈ zagierODERegularSet)
    (hode : zagierAnalyticODE f z = 0) :
    HasDerivAt (zagierODEState f) (zagierODECompanion z *ᵥ zagierODEState f z) z := by
  have h4 : deriv (deriv (deriv (deriv f))) z =
      -((zagierODECoeff 0).eval z * f z + (zagierODECoeff 1).eval z * deriv f z +
        (zagierODECoeff 2).eval z * deriv (deriv f) z +
        (zagierODECoeff 3).eval z * deriv (deriv (deriv f)) z) /
          (zagierODECoeff 4).eval z := by
    apply (eq_div_iff hz).mpr
    dsimp [zagierAnalyticODE] at hode
    linear_combination hode
  rw [zagierODECompanion_mulVec]
  change HasDerivAt (zagierODEState f)
    ![deriv f z, deriv (deriv f) z, deriv (deriv (deriv f)) z,
      -((zagierODECoeff 0).eval z * f z + (zagierODECoeff 1).eval z * deriv f z +
        (zagierODECoeff 2).eval z * deriv (deriv f) z +
        (zagierODECoeff 3).eval z * deriv (deriv (deriv f)) z) /
          (zagierODECoeff 4).eval z] z
  rw [← h4]
  exact hasDerivAt_zagierODEState hf

theorem zagierAnalyticODE_eq_zero_iff_hasDerivAt_state {f : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : z ∈ zagierODERegularSet) :
    zagierAnalyticODE f z = 0 ↔
      HasDerivAt (zagierODEState f) (zagierODECompanion z *ᵥ zagierODEState f z) z := by
  constructor
  · exact hasDerivAt_zagierODEState_of_ode hf hz
  · intro h
    have hval := (hasDerivAt_zagierODEState hf).unique h
    rw [zagierODECompanion_mulVec] at hval
    have h3 := congrFun hval (3 : Fin 4)
    change deriv (deriv (deriv (deriv f))) z =
      -((zagierODECoeff 0).eval z * f z + (zagierODECoeff 1).eval z * deriv f z +
        (zagierODECoeff 2).eval z * deriv (deriv f) z +
        (zagierODECoeff 3).eval z * deriv (deriv (deriv f)) z) /
          (zagierODECoeff 4).eval z at h3
    have hc := (eq_div_iff hz).mp h3
    dsimp [zagierAnalyticODE]
    linear_combination hc

/-- The actual descended Zagier function solves the companion system near zero. -/
theorem hasDerivAt_zagierODEState_symmetrizedAnalytic_hA {z : ℂ}
    (hz : ‖z‖ < 1 / 648) (hreg : z ∈ zagierODERegularSet) :
    HasDerivAt (zagierODEState (symmetrizedAnalytic hA))
      (zagierODECompanion z *ᵥ zagierODEState (symmetrizedAnalytic hA) z) z :=
  hasDerivAt_zagierODEState_of_ode (analyticAt_symmetrizedAnalytic_hA hz) hreg
    (zagierAnalyticODE_symmetrizedAnalytic_hA hz)

end DirichletL
