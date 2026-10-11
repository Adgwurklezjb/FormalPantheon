import Analysis.RationalFunctionCalculus

/-!
Rational evaluation in the coordinate z=1/y at infinity, for the last
rational obstruction in CDT v2, Lemma `seven` (supplied TeX lines 7990-8015).
All ring and derivative identities concern punctured germs at zero.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

theorem meromorphicAt_ratFunc_eval_inv (R : RatFunc ℂ) :
    MeromorphicAt (fun z => R.eval (RingHom.id ℂ) z⁻¹) 0 :=
  (meromorphicAt_polynomial_eval_inv R.num).div
    (meromorphicAt_polynomial_eval_inv R.denom)

/-- Rational evaluation at infinity, represented on punctured germs in the inverse coordinate. -/
noncomputable def ratFuncEvalInvGerm : RatFunc ℂ →+* Germ (𝓝[≠] (0 : ℂ)) ℂ where
  toFun R := (fun z => R.eval (RingHom.id ℂ) z⁻¹ : ℂ → ℂ)
  map_one' := by simp only [RatFunc.eval_one]; rfl
  map_zero' := by simp only [RatFunc.eval_zero]; rfl
  map_mul' R S := by
    apply Germ.coe_eq.mpr
    filter_upwards [eventually_ne_zero_polynomial_eval_inv R.denom_ne_zero,
      eventually_ne_zero_polynomial_eval_inv S.denom_ne_zero] with z hR hS
    exact RatFunc.eval_mul _ _ (by simpa using hR) (by simpa using hS)
  map_add' R S := by
    apply Germ.coe_eq.mpr
    filter_upwards [eventually_ne_zero_polynomial_eval_inv R.denom_ne_zero,
      eventually_ne_zero_polynomial_eval_inv S.denom_ne_zero] with z hR hS
    exact RatFunc.eval_add _ _ (by simpa using hR) (by simpa using hS)

theorem ratFuncEvalInvGerm_polynomial (p : ℂ[X]) :
    ratFuncEvalInvGerm (algebraMap ℂ[X] (RatFunc ℂ) p) =
      (fun z => p.eval z⁻¹ : ℂ → ℂ) := by
  apply Germ.coe_eq.mpr
  exact Eventually.of_forall (fun z => by simp only [RatFunc.eval_algebraMap, Algebra.algebraMap_self_apply, Polynomial.eval₂_id])

theorem ratFuncEvalInvGerm_derivative (R : RatFunc ℂ) :
    ratFuncEvalInvGerm (ratFuncDerivative R) =
      (fun z => -z ^ 2 * deriv (fun t => R.eval (RingHom.id ℂ) t⁻¹) z : ℂ → ℂ) := by
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_ne_zero_polynomial_eval_inv R.denom_ne_zero,
    self_mem_nhdsWithin] with z hR hz
  change z ≠ 0 at hz
  have hd := ((hasDerivAt_ratFunc_eval R hR).comp z (hasDerivAt_inv hz)).deriv
  change deriv (fun t => R.eval (RingHom.id ℂ) t⁻¹) z =
    (ratFuncDerivative R).eval (RingHom.id ℂ) z⁻¹ * (-(z ^ 2)⁻¹) at hd
  rw [hd]
  field_simp [hz]

end DirichletL
