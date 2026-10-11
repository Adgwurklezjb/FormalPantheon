import Analysis.Dilogarithm
import Analysis.MobiusDerivatives

/-!
The normalized logarithm and dilogarithm transformations underlying CDT v2,
`defB` and Lemma `seven` (supplied TeX lines 7311-7348 and 7915-7958).
These are formal identities over Q at zero, before analytic branch choices.
-/

namespace DirichletL

local notation "D" => PowerSeries.derivative ℚ
local notation "x" => (PowerSeries.X : PowerSeries ℚ)
local notation "w" => mobiusInvolutionQ
local notation "u" => (1 - mobiusInvolutionQ)
local notation "A" => pureLogarithmSeries
local notation "L" => pureDilogarithmSeries

theorem one_sub_X_mul_derivative_pureLogarithmSeries : (1 - x) * D A = 1 := by
  rw [sub_mul, one_mul]
  ext n
  cases n with
  | zero =>
    simp only [map_sub, PowerSeries.coeff_derivative, PowerSeries.coeff_zero_X_mul,
      coeff_pureLogarithmSeries]
    norm_num
  | succ n =>
    simp only [map_sub, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      coeff_pureLogarithmSeries, PowerSeries.coeff_one, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, if_false]
    push_cast
    field_simp
    ring

theorem derivative_pureLogarithmSeries : D A = u := by
  have h := one_sub_X_mul_derivative_pureLogarithmSeries
  have hu := one_sub_X_mul_one_sub_mobiusInvolutionQ
  linear_combination u * h - D A * hu

theorem X_mul_derivative_pureDilogarithmSeries : x * D L = A := by
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      coeff_pureDilogarithmSeries, coeff_pureLogarithmSeries]
    push_cast
    field_simp

theorem subst_pureLogarithmSeries_mobiusInvolutionQ :
    MvPowerSeries.subst (fun (_ : Unit) => w) A = -A := by
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  have hs : MvPowerSeries.subst (fun (_ : Unit) => w) u = 1 - x := by
    rw [← MvPowerSeries.substAlgHom_apply hw]
    simp only [map_sub, map_one, MvPowerSeries.substAlgHom_apply,
      mobiusInvolutionQ_subst_self]
  have hd : D (MvPowerSeries.subst (fun (_ : Unit) => w) A) =
      MvPowerSeries.subst (fun (_ : Unit) => w) (D A) * D w :=
    derivativeFun_subst A w constantCoeff_mobiusInvolutionQ
  apply PowerSeries.derivative.ext
  · rw [hd, derivative_pureLogarithmSeries, hs, map_neg,
      derivative_pureLogarithmSeries, derivative_mobiusInvolutionQ]
    linear_combination -u * one_sub_X_mul_one_sub_mobiusInvolutionQ
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_subst_zero constantCoeff_mobiusInvolutionQ]
    simp [pureLogarithmSeries]

/-- The normalized dilogarithm trace is minus one half of the squared logarithm. -/
theorem two_mul_symmetrizedFormal_pureDilogarithmSeries :
    2 * symmetrizedFormal L = -A ^ 2 := by
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => w) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  let s : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := MvPowerSeries.substAlgHom hw
  have hs (f : PowerSeries ℚ) : s f = MvPowerSeries.subst (fun (_ : Unit) => w) f :=
    MvPowerSeries.substAlgHom_apply hw f
  have hsx : s x = w := MvPowerSeries.substAlgHom_X hw ()
  have hsa : s A = -A := (hs A).trans subst_pureLogarithmSeries_mobiusInvolutionQ
  have he : w * s (D L) = -A := by
    have h := congrArg s X_mul_derivative_pureDilogarithmSeries
    rw [map_mul, hsx, hsa] at h
    exact h
  have hd : D (s L) = s (D L) * (-u ^ 2) := by
    rw [hs, hs, ← derivative_mobiusInvolutionQ]
    exact derivativeFun_subst L w constantCoeff_mobiusInvolutionQ
  change 2 * (L + MvPowerSeries.subst (fun (_ : Unit) => w) L) = -A ^ 2
  rw [← hs]
  apply PowerSeries.derivative.ext
  · apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℚ))
    have ht : D (2 : PowerSeries ℚ) = 0 := (PowerSeries.derivative ℚ).map_natCast 2
    simp only [Derivation.leibniz, map_add, ht, smul_eq_mul,
      zero_mul, add_zero, hd, map_neg, Derivation.leibniz_pow,
      derivative_pureLogarithmSeries, nsmul_eq_mul]
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, pow_one]
    linear_combination 2 * X_mul_derivative_pureDilogarithmSeries -
      2 * u ^ 2 * (x - 1) * he +
      2 * u ^ 2 * s (D L) * X_sub_one_mul_mobiusInvolutionQ +
      (-2 * A * (u + 1)) * one_sub_X_mul_one_sub_mobiusInvolutionQ
  · have h0 : PowerSeries.constantCoeff (R := ℚ) (s L) = 0 := by
      rw [hs, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        coeff_subst_zero constantCoeff_mobiusInvolutionQ]
      simp
    rw [map_mul, map_add, h0]
    simp [pureDilogarithmSeries, pureLogarithmSeries]

end DirichletL
