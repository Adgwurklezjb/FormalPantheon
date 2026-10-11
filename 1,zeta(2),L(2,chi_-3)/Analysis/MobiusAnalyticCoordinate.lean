import Analysis.AnalyticComposition

/-!
The analytic coordinate of CDT v2 equation `y in x` and its exact jet.
The pole and both ramification points are excluded when taking an inverse.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The invariant coordinate of CDT's Mobius involution. -/
noncomputable def mobiusCoordinate (z : ℂ) : ℂ := z + z / (z - 1)

theorem mobiusCoordinate_eq {z : ℂ} (hz : z ≠ 1) :
    mobiusCoordinate z = z + 1 - (1 - z)⁻¹ := by
  dsimp [mobiusCoordinate]
  field_simp [sub_ne_zero.mpr hz, sub_ne_zero.mpr hz.symm]
  ring

theorem analyticAt_mobiusCoordinate {z : ℂ} (hz : z ≠ 1) :
    AnalyticAt ℂ mobiusCoordinate z :=
  analyticAt_id.add (analyticAt_id.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hz))

theorem hasDerivAt_mobiusCoordinate {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt mobiusCoordinate (1 - (1 - z)⁻¹ ^ 2) z := by
  have he : mobiusCoordinate =ᶠ[𝓝 z] fun w => w + 1 - (1 - w)⁻¹ := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact mobiusCoordinate_eq hw
  have hu : HasDerivAt (fun w : ℂ => (1 - w)⁻¹) ((1 - z)⁻¹ ^ 2) z := by
    simpa only [neg_neg, div_eq_mul_inv, one_mul, inv_pow] using
      ((hasDerivAt_id z).const_sub 1).inv (sub_ne_zero.mpr hz.symm)
  exact (((hasDerivAt_id z).add_const 1).sub hu).congr_of_eventuallyEq he

theorem deriv_mobiusCoordinate {z : ℂ} (hz : z ≠ 1) :
    deriv mobiusCoordinate z = 1 - (1 - z)⁻¹ ^ 2 :=
  (hasDerivAt_mobiusCoordinate hz).deriv

theorem deriv_two_mobiusCoordinate {z : ℂ} (hz : z ≠ 1) :
    deriv (deriv mobiusCoordinate) z = -2 * (1 - z)⁻¹ ^ 3 := by
  have he : deriv mobiusCoordinate =ᶠ[𝓝 z] fun w => 1 - (1 - w)⁻¹ ^ 2 := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact deriv_mobiusCoordinate hw
  have hu : HasDerivAt (fun w : ℂ => (1 - w)⁻¹) ((1 - z)⁻¹ ^ 2) z := by
    simpa only [neg_neg, div_eq_mul_inv, one_mul, inv_pow] using
      ((hasDerivAt_id z).const_sub 1).inv (sub_ne_zero.mpr hz.symm)
  rw [he.deriv_eq, ((hu.fun_pow 2).const_sub 1).deriv]
  ring

theorem deriv_three_mobiusCoordinate {z : ℂ} (hz : z ≠ 1) :
    deriv (deriv (deriv mobiusCoordinate)) z = -6 * (1 - z)⁻¹ ^ 4 := by
  have he : deriv (deriv mobiusCoordinate) =ᶠ[𝓝 z] fun w => -2 * (1 - w)⁻¹ ^ 3 := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact deriv_two_mobiusCoordinate hw
  have hu : HasDerivAt (fun w : ℂ => (1 - w)⁻¹) ((1 - z)⁻¹ ^ 2) z := by
    simpa only [neg_neg, div_eq_mul_inv, one_mul, inv_pow] using
      ((hasDerivAt_id z).const_sub 1).inv (sub_ne_zero.mpr hz.symm)
  rw [he.deriv_eq, ((hu.fun_pow 3).const_mul (-2)).deriv]
  ring

theorem deriv_four_mobiusCoordinate {z : ℂ} (hz : z ≠ 1) :
    deriv (deriv (deriv (deriv mobiusCoordinate))) z = -24 * (1 - z)⁻¹ ^ 5 := by
  have he : deriv (deriv (deriv mobiusCoordinate)) =ᶠ[𝓝 z]
      fun w => -6 * (1 - w)⁻¹ ^ 4 := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact deriv_three_mobiusCoordinate hw
  have hu : HasDerivAt (fun w : ℂ => (1 - w)⁻¹) ((1 - z)⁻¹ ^ 2) z := by
    simpa only [neg_neg, div_eq_mul_inv, one_mul, inv_pow] using
      ((hasDerivAt_id z).const_sub 1).inv (sub_ne_zero.mpr hz.symm)
  rw [he.deriv_eq, ((hu.fun_pow 4).const_mul (-6)).deriv]
  ring

theorem deriv_mobiusCoordinate_ne_zero {z : ℂ} (hz₀ : z ≠ 0) (hz₁ : z ≠ 1)
    (hz₂ : z ≠ 2) : deriv mobiusCoordinate z ≠ 0 := by
  rw [deriv_mobiusCoordinate hz₁]
  intro h
  have he : z * (z - 2) = 0 := by
    field_simp [sub_ne_zero.mpr hz₁.symm] at h
    linear_combination h
  exact mul_ne_zero hz₀ (sub_ne_zero.mpr hz₂) he

end DirichletL
