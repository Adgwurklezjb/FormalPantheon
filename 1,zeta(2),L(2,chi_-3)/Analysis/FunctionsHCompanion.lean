import Analysis.AnalyticLinearODEGerms
import Analysis.ZagierEndpointSymmetry

/-!
The augmented matrix system of CDT v2 equation `defH`, with state (Y,Y',b,c).
The original forcing coefficients are constant state coordinates, and the
regular locus excludes exactly 0, 1/9, and 1.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The regular locus of CDT's original forced second-order equation. -/
def hForcedRegularSet : Set ℂ := {z | z * (1 - z) * (1 - 9 * z) ≠ 0}

theorem isOpen_hForcedRegularSet : IsOpen hForcedRegularSet :=
  isOpen_ne_fun (by fun_prop) continuous_const

theorem mem_hForcedRegularSet_iff (z : ℂ) :
    z ∈ hForcedRegularSet ↔ z ≠ 0 ∧ z ≠ 1 / 9 ∧ z ≠ 1 := by
  have h9 : 1 - 9 * z = 0 ↔ z = 1 / 9 := by
    constructor
    · intro h
      linear_combination -(1 / 9 : ℂ) * h
    · intro h
      linear_combination -(9 : ℂ) * h
  have h1 : 1 - z ≠ 0 ↔ z ≠ 1 := by rw [sub_ne_zero]; exact ne_comm
  have h9ne : 1 - 9 * z ≠ 0 ↔ z ≠ 1 / 9 := not_congr h9
  change z * (1 - z) * (1 - 9 * z) ≠ 0 ↔ _
  rw [mul_ne_zero_iff, mul_ne_zero_iff, h1, h9ne]
  tauto

/-- The original equation as a homogeneous matrix equation with two constant coordinates. -/
noncomputable def hForcedMatrix (z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0;
    -(9 * z - 3) / (z * (1 - z) * (1 - 9 * z)),
    -(1 - 20 * z + 27 * z ^ 2) / (z * (1 - z) * (1 - 9 * z)),
    1 / (z * (1 - z) * (1 - 9 * z)),
    1 / ((1 - z) * (z * (1 - z) * (1 - 9 * z)));
    0, 0, 0, 0;
    0, 0, 0, 0]

theorem hForcedMatrix_mulVec (z : ℂ) (v : Fin 4 → ℂ) :
    hForcedMatrix z *ᵥ v =
      ![v 1, (-(9 * z - 3) * v 0 - (1 - 20 * z + 27 * z ^ 2) * v 1 +
        v 2 + v 3 / (1 - z)) / (z * (1 - z) * (1 - 9 * z)), 0, 0] := by
  ext i
  fin_cases i <;> simp [hForcedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    div_eq_mul_inv, mul_inv_rev]
  ring

theorem analyticOnNhd_hForcedMatrix : AnalyticOnNhd ℂ hForcedMatrix hForcedRegularSet := by
  intro z hz
  have h1 : 1 - z ≠ 0 := sub_ne_zero.mpr (mem_hForcedRegularSet_iff z |>.mp hz).2.2.symm
  have ha : AnalyticAt ℂ (fun w : ℂ => w * (1 - w) * (1 - 9 * w)) z := by fun_prop
  have hb : AnalyticAt ℂ (fun w : ℂ => 1 - 20 * w + 27 * w ^ 2) z := by fun_prop
  have hc : AnalyticAt ℂ (fun w : ℂ => 9 * w - 3) z := by fun_prop
  have hd : AnalyticAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
  apply analyticAt_pi_iff.mpr
  intro i
  apply analyticAt_pi_iff.mpr
  intro j
  fin_cases i
  · fin_cases j <;> exact analyticAt_const
  · fin_cases j
    · exact hc.neg.div ha hz
    · exact hb.neg.div ha hz
    · exact analyticAt_const.div ha hz
    · exact analyticAt_const.div (hd.mul ha) (mul_ne_zero h1 hz)
  · fin_cases j <;> exact analyticAt_const
  · fin_cases j <;> exact analyticAt_const

/-- The actual analytic matrix data of CDT's original forced family. -/
noncomputable def hForcedSystem : AnalyticMatrixODE (Fin 4) where
  domain := hForcedRegularSet
  isOpen_domain := isOpen_hForcedRegularSet
  matrix := hForcedMatrix
  analytic := analyticOnNhd_hForcedMatrix

/-- Value, first derivative, and the two fixed forcing coefficients. -/
noncomputable def hForcedState (f : ℂ → ℂ) (b c : ℂ) (z : ℂ) : Fin 4 → ℂ :=
  ![f z, deriv f z, b, c]

theorem analyticAt_hForcedState {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (b c : ℂ) :
    AnalyticAt ℂ (hForcedState f b c) z := by
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i
  · exact hf
  · exact hf.deriv
  · exact analyticAt_const
  · exact analyticAt_const

theorem hasDerivAt_hForcedState_of_ode {f : ℂ → ℂ} {z b c : ℂ}
    (hf : AnalyticAt ℂ f z) (hz : z ∈ hForcedRegularSet)
    (hode : zagierSecondOrderODE f z = b + c / (1 - z)) :
    HasDerivAt (hForcedState f b c) (hForcedMatrix z *ᵥ hForcedState f b c z) z := by
  have h2 : deriv (deriv f) z =
      (-(9 * z - 3) * f z - (1 - 20 * z + 27 * z ^ 2) * deriv f z + b + c / (1 - z)) /
        (z * (1 - z) * (1 - 9 * z)) := by
    apply (eq_div_iff hz).mpr
    dsimp [zagierSecondOrderODE] at hode
    linear_combination hode
  rw [hForcedMatrix_mulVec]
  change HasDerivAt (hForcedState f b c)
    ![deriv f z, (-(9 * z - 3) * f z - (1 - 20 * z + 27 * z ^ 2) * deriv f z +
      b + c / (1 - z)) / (z * (1 - z) * (1 - 9 * z)), 0, 0] z
  rw [← h2]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hf.differentiableAt.hasDerivAt
  · exact hf.deriv.differentiableAt.hasDerivAt
  · exact hasDerivAt_const z b
  · exact hasDerivAt_const z c

theorem eventually_hForcedODE_of_matrix {F : ℂ → Fin 4 → ℂ} {z0 : ℂ}
    (hz0 : z0 ∈ hForcedRegularSet)
    (hode : ∀ᶠ z in 𝓝 z0, HasDerivAt F (hForcedMatrix z *ᵥ F z) z) :
    ∀ᶠ z in 𝓝 z0, zagierSecondOrderODE (fun w => F w 0) z =
      F z 2 + F z 3 / (1 - z) := by
  have hd : deriv (fun z => F z 0) =ᶠ[𝓝 z0] fun z => F z 1 := by
    filter_upwards [hode] with z hz
    simpa only [hForcedMatrix_mulVec, Matrix.cons_val_zero] using (hasDerivAt_pi.mp hz 0).deriv
  filter_upwards [hode, hd, hd.deriv, isOpen_hForcedRegularSet.mem_nhds hz0]
    with z hz hd1 hd2 hreg
  have hs := (hasDerivAt_pi.mp hz 1).deriv
  rw [hForcedMatrix_mulVec] at hs
  change deriv (fun w => F w 1) z =
    (-(9 * z - 3) * F z 0 - (1 - 20 * z + 27 * z ^ 2) * F z 1 +
      F z 2 + F z 3 / (1 - z)) / (z * (1 - z) * (1 - 9 * z)) at hs
  dsimp only [zagierSecondOrderODE]
  rw [hd2, hd1]
  have he := (eq_div_iff hreg).mp hs
  linear_combination he

end DirichletL
