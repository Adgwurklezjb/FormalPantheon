import Analysis.PolynomialOrders

/-!
Common denominators, rational evaluation, and differentiation on punctured
germs, for CDT v2, Lemma `seven` and `14functions`, equations `todiff` and `remaining`.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

/-- A finite rational family has one nonzero polynomial common denominator. -/
theorem exists_ratFunc_denominator {ι : Type*} [Finite ι] (B : ι → RatFunc ℂ) :
    ∃ Q : ℂ[X], Q ≠ 0 ∧ ∃ P : ι → ℂ[X], ∀ i,
      algebraMap ℂ[X] (RatFunc ℂ) (P i) = algebraMap ℂ[X] (RatFunc ℂ) Q * B i := by
  obtain ⟨q, hq⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℂ[X]) B
  have hp : ∀ i, ∃ p : ℂ[X],
      algebraMap ℂ[X] (RatFunc ℂ) p = algebraMap ℂ[X] (RatFunc ℂ) (q : ℂ[X]) * B i := by
    intro i
    obtain ⟨p, hp⟩ := hq i
    exact ⟨p, by simpa only [Algebra.smul_def] using hp⟩
  choose P hP using hp
  exact ⟨q, nonZeroDivisors.ne_zero q.property, P, hP⟩

theorem ratFunc_eval_polynomial_div (p q : ℂ[X]) {z : ℂ} (hq : q.eval z ≠ 0) :
    (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q).eval
      (RingHom.id ℂ) z = p.eval z / q.eval z := by
  let B := algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q
  have hq0 : q ≠ 0 := fun h => hq (by simp [h])
  have hd : B.denom.eval z ≠ 0 := by
    intro h
    exact hq (eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_div_dvd p q) h)
  have he := congrArg (Polynomial.eval z)
    ((RatFunc.num_mul_eq_mul_denom_iff hq0).mpr (show B = _ from rfl))
  change B.num.eval z / B.denom.eval z = p.eval z / q.eval z
  apply (div_eq_div_iff hd hq).mpr
  simpa only [eval_mul] using he

/-- The quotient-rule rational representative of the analytic derivative. -/
noncomputable def ratFuncDerivative (B : RatFunc ℂ) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) (B.num.derivative * B.denom - B.num * B.denom.derivative) /
    algebraMap ℂ[X] (RatFunc ℂ) (B.denom ^ 2)

theorem denom_ratFuncDerivative_dvd (B : RatFunc ℂ) :
    (ratFuncDerivative B).denom ∣ B.denom ^ 2 :=
  RatFunc.denom_div_dvd _ _

theorem hasDerivAt_ratFunc_eval (B : RatFunc ℂ) {z : ℂ} (hz : B.denom.eval z ≠ 0) :
    HasDerivAt (fun w => B.eval (RingHom.id ℂ) w)
      ((ratFuncDerivative B).eval (RingHom.id ℂ) z) z := by
  rw [ratFuncDerivative, ratFunc_eval_polynomial_div _ _
    (by simpa only [eval_pow] using pow_ne_zero 2 hz)]
  simpa only [eval_sub, eval_mul, eval_pow] using
    (B.num.hasDerivAt z).div (B.denom.hasDerivAt z) hz

theorem meromorphicAt_ratFunc_eval (B : RatFunc ℂ) (a : ℂ) :
    MeromorphicAt (fun z => B.eval (RingHom.id ℂ) z) a :=
  ((AnalyticOnNhd.eval_polynomial B.num) a (Set.mem_univ a)).meromorphicAt.div
    ((AnalyticOnNhd.eval_polynomial B.denom) a (Set.mem_univ a)).meromorphicAt

/-- Rational evaluation is a ring homomorphism on punctured-neighborhood germs. -/
noncomputable def ratFuncEvalGerm (w : ℂ) : RatFunc ℂ →+* Germ (𝓝[≠] w) ℂ where
  toFun B := (fun z => B.eval (RingHom.id ℂ) z : ℂ → ℂ)
  map_one' := by simp only [RatFunc.eval_one]; rfl
  map_mul' A B := by
    apply Germ.coe_eq.mpr
    filter_upwards [eventually_ne_zero_polynomial_eval A.denom_ne_zero w,
      eventually_ne_zero_polynomial_eval B.denom_ne_zero w] with z hA hB
    exact RatFunc.eval_mul _ _ (by simpa using hA) (by simpa using hB)
  map_zero' := by simp only [RatFunc.eval_zero]; rfl
  map_add' A B := by
    apply Germ.coe_eq.mpr
    filter_upwards [eventually_ne_zero_polynomial_eval A.denom_ne_zero w,
      eventually_ne_zero_polynomial_eval B.denom_ne_zero w] with z hA hB
    exact RatFunc.eval_add _ _ (by simpa using hA) (by simpa using hB)

theorem ratFuncEvalGerm_polynomial_div (p : ℂ[X]) {q : ℂ[X]} (hq : q ≠ 0) (w : ℂ) :
    ratFuncEvalGerm w (algebraMap ℂ[X] (RatFunc ℂ) p / algebraMap ℂ[X] (RatFunc ℂ) q) =
      (fun z => p.eval z / q.eval z : ℂ → ℂ) := by
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_ne_zero_polynomial_eval hq w] with z hz
  exact ratFunc_eval_polynomial_div p q hz

theorem ratFuncEvalGerm_derivative (B : RatFunc ℂ) (w : ℂ) :
    ratFuncEvalGerm w (ratFuncDerivative B) =
      (fun z => deriv (fun x => B.eval (RingHom.id ℂ) x) z : ℂ → ℂ) := by
  apply Germ.coe_eq.mpr
  filter_upwards [eventually_ne_zero_polynomial_eval B.denom_ne_zero w] with z hz
  exact (hasDerivAt_ratFunc_eval B hz).deriv.symm

theorem ratFuncEvalGerm_injective (w : ℂ) : Function.Injective (ratFuncEvalGerm w) :=
  (ratFuncEvalGerm w).injective

end DirichletL
