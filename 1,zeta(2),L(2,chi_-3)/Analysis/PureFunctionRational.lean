import Analysis.RationalFunctionPullback
import Analysis.RationalFunctionInfinity
import Analysis.MeromorphicPrimitives

/-!
The two rational obstructions at the end of CDT v2, Lemma `seven`
(supplied TeX lines 7990-8015). The second compares the constant and
linear coefficients at infinity, as checked in the mathematical deviation note.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

theorem eq_zero_of_X_mul_ratFuncDerivative_eq (R : RatFunc ℂ) (a : ℂ)
    (hR : RatFunc.X * ratFuncDerivative R = algebraMap ℂ (RatFunc ℂ) a) : a = 0 := by
  have ha : ratFuncEvalGerm 0 (algebraMap ℂ (RatFunc ℂ) a) = (fun _ : ℂ => a : ℂ → ℂ) := by
    simpa only [RatFunc.algebraMap_C, RatFunc.C, eval_C] using
      ratFuncEvalGerm_polynomial (C a) 0
  have he := congrArg (ratFuncEvalGerm 0) hR
  rw [map_mul, ratFuncEvalGerm_X, ratFuncEvalGerm_derivative, ha] at he
  obtain ⟨_, _, _, hzero⟩ := exists_analyticAt_eventuallyEq_of_analytic_mul_deriv
    (meromorphicAt_ratFunc_eval R 0) (analyticAt_const (v := a)) (by
      simpa only [sub_zero] using Germ.coe_eq.mp he)
  exact hzero

/-- The resonance at infinity in the B4 equation forces the constant forcing to vanish. -/
theorem eq_zero_of_meromorphic_pureB4_inverse_ode {b : ℂ → ℂ} (hb : MeromorphicAt b 0)
    (a : ℂ)
    (hode : (fun z => z * (1 - 4 * z) * deriv b z + (2 * z - 1) * b z) =ᶠ[𝓝[≠] 0]
      fun z => a * (4 * z - 1)) : a = 0 := by
  have hp : AnalyticAt ℂ (fun z : ℂ => 1 - 4 * z) 0 :=
    analyticAt_const.sub (analyticAt_const.mul analyticAt_id)
  have hq : AnalyticAt ℂ (fun z : ℂ => 2 * z - 1) 0 :=
    (analyticAt_const.mul analyticAt_id).sub analyticAt_const
  have hg : AnalyticAt ℂ (fun z : ℂ => a * (4 * z - 1)) 0 :=
    analyticAt_const.mul ((analyticAt_const.mul analyticAt_id).sub analyticAt_const)
  obtain ⟨f, hf, hbf⟩ := exists_analyticAt_eventuallyEq_of_meromorphic_regular_singular
    hb hp hq hg (by
      intro N hN h
      have h1 : (N : ℂ) = 1 := sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)
      have hi : N = 1 := by exact_mod_cast h1
      omega) (by simpa only [sub_zero] using hode)
  have he : (fun z => z * (1 - 4 * z) * deriv f z + (2 * z - 1) * f z) =ᶠ[𝓝[≠] 0]
      fun z => a * (4 * z - 1) := by
    filter_upwards [hode, hbf, eventuallyEq_deriv_of_punctured hbf] with z hz hz0 hz1
    rwa [hz0, hz1] at hz
  have hleft : AnalyticAt ℂ
      (fun z => z * (1 - 4 * z) * deriv f z + (2 * z - 1) * f z) 0 :=
    ((analyticAt_id.mul hp).mul hf.deriv).add (hq.mul hf)
  have hefull : (fun z => z * (1 - 4 * z) * deriv f z + (2 * z - 1) * f z) =ᶠ[𝓝 0]
      (fun z => a * (4 * z - 1)) :=
    (hleft.frequently_eq_iff_eventually_eq hg).mp he.frequently
  have h0 : f 0 = a := by
    have h := hefull.self_of_nhds
    simpa using h
  have hd := hefull.deriv.self_of_nhds
  have hpoly := (hasDerivAt_id (0 : ℂ)).fun_mul
    ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).fun_sub ((hasDerivAt_id (0 : ℂ)).const_mul 4))
  have hlin := ((hasDerivAt_id (0 : ℂ)).const_mul 2).sub_const 1
  have hl := ((hpoly.fun_mul hf.deriv.differentiableAt.hasDerivAt).fun_add
    (hlin.fun_mul hf.differentiableAt.hasDerivAt)).deriv
  have hr := ((((hasDerivAt_id (0 : ℂ)).const_mul 4).sub_const 1).const_mul a).deriv
  simp only [id_eq] at hl hr
  rw [hl, hr] at hd
  norm_num only [mul_zero, zero_mul, sub_zero, zero_sub, one_mul, mul_one,
    zero_add, add_zero, neg_one_mul] at hd
  rw [h0] at hd
  linear_combination -(1 / 2 : ℂ) * hd

/-- The B4 coefficient equation has no rational solution for a nonzero constant forcing. -/
theorem eq_zero_of_ratFunc_pureB4_primitive_ode (R : RatFunc ℂ) (a : ℂ)
    (hR : RatFunc.X * (4 - RatFunc.X) * ratFuncDerivative R + (2 - RatFunc.X) * R =
      algebraMap ℂ (RatFunc ℂ) a * (4 - RatFunc.X)) : a = 0 := by
  have hx : ratFuncEvalInvGerm RatFunc.X = (fun z : ℂ => z⁻¹ : ℂ → ℂ) := by
    simpa only [RatFunc.algebraMap_X, eval_X] using ratFuncEvalInvGerm_polynomial X
  have ha : ratFuncEvalInvGerm (algebraMap ℂ (RatFunc ℂ) a) =
      (fun _ : ℂ => a : ℂ → ℂ) := by
    simpa only [RatFunc.algebraMap_C, RatFunc.C, eval_C] using ratFuncEvalInvGerm_polynomial (C a)
  have he := congrArg ratFuncEvalInvGerm hR
  simp only [map_add, map_mul, map_sub, map_ofNat, hx, ha, ratFuncEvalInvGerm_derivative] at he
  apply eq_zero_of_meromorphic_pureB4_inverse_ode (meromorphicAt_ratFunc_eval_inv R) a
  filter_upwards [Germ.coe_eq.mp he, self_mem_nhdsWithin] with z hz hz0
  change z ≠ 0 at hz0
  change z⁻¹ * (4 - z⁻¹) * (-z ^ 2 * deriv (fun t => R.eval (RingHom.id ℂ) t⁻¹) z) +
    (2 - z⁻¹) * R.eval (RingHom.id ℂ) z⁻¹ = a * (4 - z⁻¹) at hz
  field_simp [hz0] at hz
  simp only [one_div] at hz
  linear_combination hz

end DirichletL
