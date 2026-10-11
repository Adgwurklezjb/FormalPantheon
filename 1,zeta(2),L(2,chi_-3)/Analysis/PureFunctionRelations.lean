import Analysis.PureFunctionAnalyticDifferential
import Analysis.PureFunctionDescentIndependence

/-!
Differentiated pure-function relations in CDT v2, Lemma `seven`,
equations `simpledif`, `lasttwo`, and `lasttwotwo` (supplied TeX lines 7955-8015).
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

/-- The first five descended functions, in CDT's order. -/
noncomputable def pureFiveDescentFamily : Fin 5 → ℂ → ℂ :=
  ![1, pureB2, pureB3, pureB4, pureB5]

theorem analyticAt_pureFiveDescentFamily (i : Fin 5) :
    AnalyticAt ℂ (pureFiveDescentFamily i) 0 := by
  fin_cases i
  · exact analyticAt_const
  · exact analyticAt_pureB2 (by norm_num)
  · exact analyticAt_pureB3 (by norm_num)
  · exact analyticAt_pureB4
  · exact analyticAt_pureB5 (by norm_num)

theorem eq_zero_of_pureFiveDescentFamilyRelation (R : Fin 5 → RatFunc ℂ)
    (hrel : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      ∑ i, (R i).eval (RingHom.id ℂ) z * pureFiveDescentFamily i z = 0) : R = 0 := by
  apply eq_zero_of_ratFunc_pureDescent_relation
  filter_upwards [hrel] with z hz
  simpa [Fin.sum_univ_succ, pureFiveDescentFamily, add_assoc] using hz

/-- The common reciprocal leading coefficient for the four source differential equations. -/
noncomputable def pureDerivativeInverse : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) 1 / algebraMap ℂ[X] (RatFunc ℂ) (2 * X * (4 - X))

theorem ratFuncEvalGerm_pureDerivativeInverse :
    ratFuncEvalGerm 0 pureDerivativeInverse = (fun z : ℂ => 1 / (2 * z * (4 - z)) : ℂ → ℂ) := by
  have hp : (2 * X * (4 - X) : ℂ[X]) ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℂ[X] => p.eval 1) h
    norm_num at he
  simpa only [pureDerivativeInverse, eval_one, eval_mul, eval_ofNat, eval_X, eval_sub] using
    ratFuncEvalGerm_polynomial_div 1 hp 0

/-- The coefficient vector after differentiating a polynomially weighted primitive relation. -/
noncomputable def purePrimitiveRelationStep (P : Fin 2 → ℂ[X]) (R : Fin 5 → RatFunc ℂ) :
    Fin 5 → RatFunc ℂ :=
  let x := RatFunc.X
  let d := pureDerivativeInverse
  ![ratFuncDerivative (R 0) + d *
      (2 * x ^ 2 * R 1 + 4 * x * R 2 - 4 * x * (4 - x) * R 3 + 4 * x * R 4),
    ratFuncDerivative (R 1) + d *
      (2 * (2 - x) * R 1 - 2 * R 2 + 2 * (4 - x) * R 3 - 2 * R 4),
    ratFuncDerivative (R 2) - algebraMap ℂ[X] (RatFunc ℂ) (P 0) / x,
    ratFuncDerivative (R 3) + d * 2 * (2 - x) * R 3 -
      algebraMap ℂ[X] (RatFunc ℂ) (P 1) / x,
    ratFuncDerivative (R 4) + d * (4 - x) * R 4]

theorem purePrimitiveRelation_deriv (P : Fin 2 → ℂ[X]) (R : Fin 5 → RatFunc ℂ)
    (J : Fin 2 → ℂ → ℂ)
    (hJ : ∀ j, ∀ᶠ z : ℂ in 𝓝[≠] 0, HasDerivAt (J j) (![pureB3, pureB4] j z / z) z)
    (hrel : (fun z => ∑ j, (P j).eval z * J j z) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z => ∑ i, (R i).eval (RingHom.id ℂ) z * pureFiveDescentFamily i z) :
    (fun z => ∑ j, (P j).derivative.eval z * J j z) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z => ∑ i, (purePrimitiveRelationStep P R i).eval (RingHom.id ℂ) z *
        pureFiveDescentFamily i z := by
  have hP (j : Fin 2) : ratFuncEvalGerm 0
      (algebraMap ℂ[X] (RatFunc ℂ) (P j) / RatFunc.X) =
      (fun z => (P j).eval z / z : ℂ → ℂ) := by
    simpa only [RatFunc.algebraMap_X, eval_X] using
      ratFuncEvalGerm_polynomial_div (P j) (X_ne_zero : (X : ℂ[X]) ≠ 0) 0
  have hC : ∀ᶠ z : ℂ in 𝓝[≠] 0, ∀ i : Fin 5,
      (purePrimitiveRelationStep P R i).eval (RingHom.id ℂ) z =
        ![(ratFuncDerivative (R 0)).eval (RingHom.id ℂ) z + (1 / (2 * z * (4 - z))) *
            (2 * z ^ 2 * (R 1).eval (RingHom.id ℂ) z + 4 * z * (R 2).eval (RingHom.id ℂ) z -
              4 * z * (4 - z) * (R 3).eval (RingHom.id ℂ) z + 4 * z * (R 4).eval (RingHom.id ℂ) z),
          (ratFuncDerivative (R 1)).eval (RingHom.id ℂ) z + (1 / (2 * z * (4 - z))) *
            (2 * (2 - z) * (R 1).eval (RingHom.id ℂ) z - 2 * (R 2).eval (RingHom.id ℂ) z +
              2 * (4 - z) * (R 3).eval (RingHom.id ℂ) z - 2 * (R 4).eval (RingHom.id ℂ) z),
          (ratFuncDerivative (R 2)).eval (RingHom.id ℂ) z - (P 0).eval z / z,
          (ratFuncDerivative (R 3)).eval (RingHom.id ℂ) z +
            (1 / (2 * z * (4 - z))) * 2 * (2 - z) * (R 3).eval (RingHom.id ℂ) z - (P 1).eval z / z,
          (ratFuncDerivative (R 4)).eval (RingHom.id ℂ) z +
            (1 / (2 * z * (4 - z))) * (4 - z) * (R 4).eval (RingHom.id ℂ) z] i := by
    apply eventually_all.mpr
    intro i
    fin_cases i <;> apply Germ.coe_eq.mp
    all_goals
      change ratFuncEvalGerm 0 _ = _
      simp only [purePrimitiveRelationStep, Matrix.cons_val_zero', Matrix.cons_val_succ',
        map_add, map_sub, map_mul, map_pow, map_ofNat, ratFuncEvalGerm_X,
        ratFuncEvalGerm_pureDerivativeInverse, hP]
      rfl
  filter_upwards [eventuallyEq_deriv_of_punctured hrel, eventually_all.mpr hJ, hC,
    eventually_all.mpr (fun i => eventually_ne_zero_polynomial_eval (R i).denom_ne_zero 0),
    eventually_all.mpr (fun i =>
      (analyticAt_pureFiveDescentFamily i).eventually_analyticAt.filter_mono nhdsWithin_le_nhds),
    pureB2_ode.filter_mono nhdsWithin_le_nhds, pureB3_ode.filter_mono nhdsWithin_le_nhds,
    pureB4_ode.filter_mono nhdsWithin_le_nhds, pureB5_ode.filter_mono nhdsWithin_le_nhds,
    (eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 4)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hJz hCz hden hF h2 h3 h4 h5 hz4 hz0
  change z ≠ 0 at hz0
  have hp : z * (4 - z) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr hz4.symm)
  have h2' : deriv pureB2 z = ((2 - z) * pureB2 z + z ^ 2) / (z * (4 - z)) :=
    (eq_div_iff hp).mpr (by linear_combination h2)
  have h3' : deriv pureB3 z = (-pureB2 z + 2 * z) / (z * (4 - z)) :=
    (eq_div_iff hp).mpr (by linear_combination h3)
  have h4' : deriv pureB4 z =
      ((2 - z) * pureB4 z + (4 - z) * pureB2 z - 2 * z * (4 - z)) / (z * (4 - z)) :=
    (eq_div_iff hp).mpr (by linear_combination h4)
  have h5' : deriv pureB5 z = ((4 - z) * pureB5 z - 2 * pureB2 z + 4 * z) /
      (2 * z * (4 - z)) :=
    (eq_div_iff (by simpa only [mul_assoc] using mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hp)).mpr
      (by linear_combination h5)
  have hL := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => ((P j).hasDerivAt z).fun_mul (hJz j))).deriv
  have hR := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hasDerivAt_ratFunc_eval (R i) (hden i)).fun_mul
      (hF i).differentiableAt.hasDerivAt)).deriv
  rw [hL, hR] at hz
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, pureFiveDescentFamily,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Pi.one_apply, deriv_const, deriv_one, Pi.zero_apply,
    mul_one, mul_zero, add_zero, zero_add, h2', h3', h4', h5'] at hz
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hCz, pureFiveDescentFamily,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero', Matrix.cons_val_succ',
    Pi.one_apply, mul_one, add_zero]
  simp only [div_eq_mul_inv, mul_inv_rev] at hz ⊢
  linear_combination (norm := ring_nf!) hz

end DirichletL
