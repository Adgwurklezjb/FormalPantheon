import Analysis.RationalFunctionCalculus
import Analysis.MeromorphicPrimitives

/-!
The rational homogeneous equation attached to CDT v2, `odeJ`, in the
proof of Lemma `seven` (supplied TeX lines 7385-7387 and 7941-7957).
Integer meromorphic orders exclude the exponent one half at x=1.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

/-- The zeroth-order coefficient in the first-order J equation. -/
noncomputable def pureJCoefficient : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) 1 / algebraMap ℂ[X] (RatFunc ℂ) (2 * (X - 1))

theorem ratFuncEvalGerm_pureJCoefficient (w : ℂ) :
    ratFuncEvalGerm w pureJCoefficient =
      ((fun z : ℂ => 1 / (2 * (z - 1))) : Germ (𝓝[≠] w) ℂ) := by
  have hq : (2 * (X - 1) : ℂ[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : ℂ[X] => p.coeff 1) h
    norm_num [mul_sub, coeff_one] at hc
  simpa [pureJCoefficient] using ratFuncEvalGerm_polynomial_div 1 hq w

/-- A rational solution of the homogeneous J equation must be zero. -/
theorem eq_zero_of_ratFuncDerivative_eq_pureJCoefficient_mul (B : RatFunc ℂ)
    (hB : ratFuncDerivative B = pureJCoefficient * B) : B = 0 := by
  have he := congrArg (ratFuncEvalGerm 1) hB
  rw [ratFuncEvalGerm_derivative, map_mul, ratFuncEvalGerm_pureJCoefficient] at he
  apply ratFuncEvalGerm_injective 1
  rw [map_zero]
  apply Germ.coe_eq.mpr
  apply eventuallyEq_zero_of_meromorphic_euler (c := 1 / 2) (meromorphicAt_ratFunc_eval B 1)
  · intro N hN
    have hc : (2 : ℂ) * (N : ℂ) = 1 := by linear_combination 2 * hN
    have hi : 2 * N = 1 := by exact_mod_cast hc
    omega
  · filter_upwards [Germ.coe_eq.mp he, self_mem_nhdsWithin] with z hz hz1
    have h1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    rw [hz]
    field_simp [h1]

end DirichletL
