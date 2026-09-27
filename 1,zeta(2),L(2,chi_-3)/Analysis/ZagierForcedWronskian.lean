import Analysis.ZagierReciprocalSymmetry
import Analysis.ZagierWronskian
import Analysis.AnalyticContinuation

/-!
Actual homogeneous factors and the Wronskian derivatives for the forcing
in CDT v2, Proposition `functionsH`. The analytic remainders isolate the
two logarithmic periods needed in the nonzero-branch step of `14functions`.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The original homogeneous solution expressed near infinity by reciprocal symmetry. -/
noncomputable def zagierInfinitySolution : ℂ → ℂ :=
  zagierReciprocalTransform zagierAnalytic

theorem analyticAt_zagierInfinitySolution {z : ℂ} (hz : z ≠ 0)
    (hn : ‖zagierReciprocalCoordinate z‖ < 1 / 9) :
    AnalyticAt ℂ zagierInfinitySolution z :=
  analyticAt_zagierReciprocalTransform hz (analyticAt_zagierAnalytic hn)

theorem zagierInfinitySolution_ode {z : ℂ} (hz : z ≠ 0)
    (hn : ‖zagierReciprocalCoordinate z‖ < 1 / 9) :
    zagierSecondOrderODE zagierInfinitySolution z = 0 := by
  rw [zagierInfinitySolution,
    zagierSecondOrderODE_reciprocalTransform hz (analyticAt_zagierAnalytic hn)]
  rw [show zagierSecondOrderODE zagierAnalytic (zagierReciprocalCoordinate z) = 0 from
    zagierAnalytic_ode hn, zero_div]

theorem zagierInfinitySolution_reciprocal (z : ℂ) :
    zagierInfinitySolution (zagierReciprocalCoordinate z) = 9 * z * zagierAnalytic z := by
  simp only [zagierInfinitySolution, zagierReciprocalTransform, zagierReciprocalCoordinate_self]
  simp [zagierReciprocalCoordinate, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- The endpoint homogeneous solution expressed near one by reciprocal symmetry. -/
noncomputable def zagierOneSolution : ℂ → ℂ :=
  zagierReciprocalTransform zagierEndpointSolution

theorem analyticAt_zagierOneSolution_one : AnalyticAt ℂ zagierOneSolution 1 := by
  apply analyticAt_zagierReciprocalTransform (by norm_num)
  simpa only [zagierReciprocalCoordinate_one, one_div] using
    analyticAt_zagierEndpointSolution_one_div_nine

@[simp] theorem zagierOneSolution_one : zagierOneSolution 1 = 9 / 8 := by
  simp [zagierOneSolution, zagierReciprocalTransform]

theorem eventually_zagierOneSolution_ode :
    zagierSecondOrderODE zagierOneSolution =ᶠ[𝓝 (1 : ℂ)] 0 := by
  have hz : (9 : ℂ)⁻¹ ≠ 1 := by norm_num
  have hS : AnalyticAt ℂ zagierEndpointSolution (9 : ℂ)⁻¹ := by
    simpa only [one_div] using analyticAt_zagierEndpointSolution_one_div_nine
  have hn : ∀ᶠ z in 𝓝 (9 : ℂ)⁻¹, ‖zagierEndpointCoordinate z‖ < 1 / 9 :=
    (analyticAt_zagierEndpointCoordinate hz).continuousAt.norm.eventually_lt_const (by simp)
  have hSo : zagierSecondOrderODE zagierEndpointSolution =ᶠ[𝓝 (9 : ℂ)⁻¹] 0 := by
    filter_upwards [eventually_ne_nhds hz, hn] with z hz hn
    exact zagierEndpointSolution_ode hz hn
  apply eventually_zagierSecondOrderODE_reciprocalTransform (by norm_num)
  · simpa only [zagierReciprocalCoordinate_one] using hS
  · simpa only [zagierReciprocalCoordinate_one] using hSo

/-- The analytic remainder after the reciprocal Wronskian derivative's simple pole. -/
noncomputable def zagierInfinityRemainder (b c z : ℂ) : ℂ :=
  -b * dslope zagierAnalytic 0 z + 9 * c * zagierAnalytic z / (1 - 9 * z)

theorem analyticAt_zagierInfinityRemainder_zero (b c : ℂ) :
    AnalyticAt ℂ (zagierInfinityRemainder b c) 0 := by
  have hA : AnalyticAt ℂ zagierAnalytic 0 := analyticAt_zagierAnalytic (by norm_num)
  have hd : AnalyticAt ℂ (dslope zagierAnalytic 0) 0 := by
    obtain ⟨p, hp⟩ := hA
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  exact (analyticAt_const.mul hd).add ((analyticAt_const.mul hA).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (by norm_num))

/-- The analytic remainder after the Wronskian derivative's simple pole at one. -/
noncomputable def zagierOneRemainder (b c z : ℂ) : ℂ :=
  b * zagierOneSolution (1 + z) - c * dslope zagierOneSolution 1 (1 + z)

theorem analyticAt_zagierOneRemainder_zero (b c : ℂ) :
    AnalyticAt ℂ (zagierOneRemainder b c) 0 := by
  have hf := analyticAt_zagierOneSolution_one
  have hd : AnalyticAt ℂ (dslope zagierOneSolution 1) 1 := by
    obtain ⟨p, hp⟩ := hf
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hi : AnalyticAt ℂ (fun z : ℂ => 1 + z) 0 := by fun_prop
  exact (analyticAt_const.mul (hf.comp_of_eq hi (by simp))).sub
    (analyticAt_const.mul (hd.comp_of_eq hi (by simp)))

theorem hasDerivAt_zagierWeightedWronskian_reciprocal {H : ℂ → ℂ} {b c s : ℂ}
    (hs : s ≠ 0) (hn : ‖s‖ < 1 / 9)
    (hH : AnalyticAt ℂ H (zagierReciprocalCoordinate s))
    (hHo : zagierSecondOrderODE H (zagierReciprocalCoordinate s) =
      b + c / (1 - zagierReciprocalCoordinate s)) :
    HasDerivAt (fun z => zagierWeightedWronskian zagierInfinitySolution H
      (zagierReciprocalCoordinate z)) (-b / s + zagierInfinityRemainder b c s) s := by
  have hq := zagierReciprocalCoordinate_ne_zero hs
  have hnq : ‖zagierReciprocalCoordinate (zagierReciprocalCoordinate s)‖ < 1 / 9 := by
    simpa only [zagierReciprocalCoordinate_self] using hn
  have hf := analyticAt_zagierInfinitySolution hq hnq
  have hfo := zagierInfinitySolution_ode hq hnq
  have h := (hasDerivAt_zagierWeightedWronskian hf hH).comp s
    (hasDerivAt_zagierReciprocalCoordinate hs)
  rw [hHo, hfo, mul_zero, sub_zero, zagierInfinitySolution_reciprocal] at h
  have hs9 : 1 - 9 * s ≠ 0 := by
    intro he
    have he' : s = (9 : ℂ)⁻¹ := by linear_combination -(1 / 9 : ℂ) * he
    rw [he'] at hn
    norm_num at hn
  have hs9' : 9 * s - 1 ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hs9).symm
  convert h using 1
  simp only [zagierInfinityRemainder, dslope_of_ne _ hs, slope, vsub_eq_sub, sub_zero,
    smul_eq_mul, zagierAnalytic_zero]
  dsimp [zagierReciprocalCoordinate]
  ring_nf at hs9 hs9' ⊢
  field_simp [hs, hs9, hs9']
  linear_combination -(zagierAnalytic s * s * c * 9) * (mul_inv_cancel₀ hs9')

theorem hasDerivAt_zagierWeightedWronskian_one {H : ℂ → ℂ} {b c s : ℂ}
    (hs : s ≠ 0) (hf : AnalyticAt ℂ zagierOneSolution (1 + s))
    (hfo : zagierSecondOrderODE zagierOneSolution (1 + s) = 0)
    (hH : AnalyticAt ℂ H (1 + s))
    (hHo : zagierSecondOrderODE H (1 + s) = b + c / (1 - (1 + s))) :
    HasDerivAt (fun z => zagierWeightedWronskian zagierOneSolution H (1 + z))
      (-(c * (9 / 8)) / s + zagierOneRemainder b c s) s := by
  have h := (hasDerivAt_zagierWeightedWronskian hf hH).comp s
    ((hasDerivAt_id s).const_add 1)
  rw [hHo, hfo, mul_zero, sub_zero, mul_one] at h
  have hs1 : 1 + s ≠ 1 := by
    intro he
    apply hs
    linear_combination he
  convert h using 1
  simp only [zagierOneRemainder, dslope_of_ne _ hs1, slope, vsub_eq_sub, smul_eq_mul,
    zagierOneSolution_one]
  field_simp [hs]
  ring

theorem AnalyticContinuationAlong.zagierWeightedWronskian
    {T : Type*} [TopologicalSpace T] {γ : T → ℂ} {f g : T → ℂ → ℂ}
    (hf : AnalyticContinuationAlong γ f) (hg : AnalyticContinuationAlong γ g) :
    AnalyticContinuationAlong γ (fun t => DirichletL.zagierWeightedWronskian (f t) (g t)) := by
  refine ⟨hf.continuous, ?_, ?_⟩
  · intro t
    have ha : AnalyticAt ℂ (fun z : ℂ => z * (1 - z) * (1 - 9 * z)) (γ t) := by fun_prop
    exact ha.mul (((hf.analytic t).mul (hg.analytic t).deriv).sub
      ((hf.analytic t).deriv.mul (hg.analytic t)))
  · intro t
    filter_upwards [hf.locally_eq t, hg.locally_eq t] with s hfs hgs
    filter_upwards [hfs, hgs, hfs.deriv, hgs.deriv] with z hfz hgz hfd hgd
    simp only [DirichletL.zagierWeightedWronskian, hfz, hgz, hfd, hgd]

end DirichletL
