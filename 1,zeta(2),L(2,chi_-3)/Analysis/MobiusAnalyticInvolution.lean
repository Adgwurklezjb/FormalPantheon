import Analysis.MobiusAnalyticCoordinate

/-!
The analytic sheet involution in CDT v2, `involutionfirst` and `y in x`.
All geometric identities below exclude its pole at one.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- The rational sheet involution, using totalized complex division. -/
noncomputable def mobiusAnalyticInvolution (z : ℂ) : ℂ := z / (z - 1)

theorem analyticAt_mobiusAnalyticInvolution {z : ℂ} (hz : z ≠ 1) :
    AnalyticAt ℂ mobiusAnalyticInvolution z :=
  analyticAt_id.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hz)

theorem hasDerivAt_mobiusAnalyticInvolution {z : ℂ} (hz : z ≠ 1) :
    HasDerivAt mobiusAnalyticInvolution (-(z - 1)⁻¹ ^ 2) z := by
  convert (hasDerivAt_id z).div ((hasDerivAt_id z).sub_const 1)
    (sub_ne_zero.mpr hz) using 1
  dsimp only [id_eq]
  field_simp
  ring

theorem deriv_mobiusAnalyticInvolution {z : ℂ} (hz : z ≠ 1) :
    deriv mobiusAnalyticInvolution z = -(z - 1)⁻¹ ^ 2 :=
  (hasDerivAt_mobiusAnalyticInvolution hz).deriv

theorem deriv_two_mobiusAnalyticInvolution {z : ℂ} (hz : z ≠ 1) :
    deriv (deriv mobiusAnalyticInvolution) z = 2 * (z - 1)⁻¹ ^ 3 := by
  have he : deriv mobiusAnalyticInvolution =ᶠ[𝓝 z] fun w => -(w - 1)⁻¹ ^ 2 := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact deriv_mobiusAnalyticInvolution hw
  have hi : HasDerivAt (fun w : ℂ => (w - 1)⁻¹) (-1 / (z - 1) ^ 2) z :=
    ((hasDerivAt_id z).sub_const 1).inv (sub_ne_zero.mpr hz)
  rw [he.deriv_eq, ((hi.fun_pow 2).fun_neg).deriv]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp [sub_ne_zero.mpr hz] <;> ring

theorem mobiusAnalyticInvolution_ne_one {z : ℂ} (hz : z ≠ 1) :
    mobiusAnalyticInvolution z ≠ 1 := by
  intro he
  have h := (div_eq_iff (sub_ne_zero.mpr hz)).mp he
  apply (one_ne_zero : (1 : ℂ) ≠ 0)
  linear_combination h

theorem mobiusAnalyticInvolution_involutive {z : ℂ} (hz : z ≠ 1) :
    mobiusAnalyticInvolution (mobiusAnalyticInvolution z) = z := by
  dsimp only [mobiusAnalyticInvolution]
  field_simp [sub_ne_zero.mpr hz]
  ring

theorem mobiusCoordinate_mobiusAnalyticInvolution {z : ℂ} (hz : z ≠ 1) :
    mobiusCoordinate (mobiusAnalyticInvolution z) = mobiusCoordinate z := by
  change mobiusAnalyticInvolution z + mobiusAnalyticInvolution (mobiusAnalyticInvolution z) =
    z + mobiusAnalyticInvolution z
  rw [mobiusAnalyticInvolution_involutive hz, add_comm]

end DirichletL
