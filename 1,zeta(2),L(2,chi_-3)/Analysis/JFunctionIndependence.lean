import Analysis.JFunction
import Analysis.JFunctionRational
import Analysis.DilogarithmIndependence

/-!
The fifth pure function in CDT v2, Lemma `seven` and equation `odeJ`
(supplied TeX lines 7385-7387 and 7941-7957). The differential order
argument and the normalization are recorded in `M4-fifth-pure-function.md`.
-/

namespace DirichletL

open Polynomial Filter Set
open scoped Topology

private theorem eq_zero_of_ratFunc_pureFour_relation (R : Fin 4 → RatFunc ℂ)
    (hrel : ∀ᶠ z : ℂ in 𝓝[≠] 0, (R 0).eval (RingHom.id ℂ) z +
      (R 1).eval (RingHom.id ℂ) z * Complex.log (1 - z) +
      (R 2).eval (RingHom.id ℂ) z * Complex.log (1 - z) ^ 2 +
      (R 3).eval (RingHom.id ℂ) z * pureDilogarithm z = 0) : R = 0 := by
  letI := (ratFuncEvalGerm 0).toModule
  have hc : ∀ i : Fin 4, (![R 0, -R 1, R 2, R 3] : Fin 4 → RatFunc ℂ) i = 0 :=
    (Fintype.linearIndependent_iff.mp linearIndependent_pureFourFunctions) _ (by
      simp only [Fin.sum_univ_four]
      change ratFuncEvalGerm 0 (R 0) * 1 + ratFuncEvalGerm 0 (-R 1) *
        ((fun z : ℂ => -Complex.log (1 - z)) : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
        ratFuncEvalGerm 0 (R 2) * ((fun z : ℂ => Complex.log (1 - z) ^ 2) :
          Germ (𝓝[≠] (0 : ℂ)) ℂ) + ratFuncEvalGerm 0 (R 3) *
        (pureDilogarithm : Germ (𝓝[≠] (0 : ℂ)) ℂ) = 0
      rw [map_neg]
      apply Germ.coe_eq.mpr
      simpa only [Function.comp_apply, mul_one, neg_mul, mul_neg, neg_neg] using hrel)
  funext i
  fin_cases i
  · exact hc 0
  · exact neg_eq_zero.mp (hc 1)
  · exact hc 2
  · exact hc 3

/-- Every local solution of the inhomogeneous J equation is outside the first four spans. -/
theorem not_jFunction_eq_ratFunc_pureFourCombination (R : Fin 4 → RatFunc ℂ) {F : ℂ → ℂ}
    (hF : ∀ᶠ z in 𝓝[≠] (0 : ℂ), HasDerivAt F
      (F z / (2 * (z - 1)) - Complex.log (1 - z) / z) z) :
    ¬ F =ᶠ[𝓝[≠] 0] (fun z => (R 0).eval (RingHom.id ℂ) z +
      (R 1).eval (RingHom.id ℂ) z * Complex.log (1 - z) +
      (R 2).eval (RingHom.id ℂ) z * Complex.log (1 - z) ^ 2 +
      (R 3).eval (RingHom.id ℂ) z * pureDilogarithm z) := by
  intro hrel
  let S : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) 1 / algebraMap ℂ[X] (RatFunc ℂ) X
  have hS : ratFuncEvalGerm 0 S =
      ((fun z : ℂ => 1 / z) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
    simpa only [eval_one, eval_X] using
      ratFuncEvalGerm_polynomial_div 1 (X_ne_zero : (X : ℂ[X]) ≠ 0) 0
  let C : Fin 4 → RatFunc ℂ :=
    ![ratFuncDerivative (R 0) + 2 * R 1 * pureJCoefficient - pureJCoefficient * R 0,
      ratFuncDerivative (R 1) + 4 * R 2 * pureJCoefficient - R 3 * S -
        pureJCoefficient * R 1 + S,
      ratFuncDerivative (R 2) - pureJCoefficient * R 2,
      ratFuncDerivative (R 3) - pureJCoefficient * R 3]
  have hCv : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ i : Fin 4,
      (C i).eval (RingHom.id ℂ) z =
        ![(ratFuncDerivative (R 0)).eval (RingHom.id ℂ) z +
            2 * (R 1).eval (RingHom.id ℂ) z * (1 / (2 * (z - 1))) -
            (1 / (2 * (z - 1))) * (R 0).eval (RingHom.id ℂ) z,
          (ratFuncDerivative (R 1)).eval (RingHom.id ℂ) z +
            4 * (R 2).eval (RingHom.id ℂ) z * (1 / (2 * (z - 1))) -
            (R 3).eval (RingHom.id ℂ) z * (1 / z) -
            (1 / (2 * (z - 1))) * (R 1).eval (RingHom.id ℂ) z + 1 / z,
          (ratFuncDerivative (R 2)).eval (RingHom.id ℂ) z -
            (1 / (2 * (z - 1))) * (R 2).eval (RingHom.id ℂ) z,
          (ratFuncDerivative (R 3)).eval (RingHom.id ℂ) z -
            (1 / (2 * (z - 1))) * (R 3).eval (RingHom.id ℂ) z] i := by
    apply eventually_all.mpr
    intro i
    fin_cases i <;> apply Germ.coe_eq.mp
    all_goals
      change ratFuncEvalGerm 0 _ = _
      simp only [C, Matrix.cons_val_zero', Matrix.cons_val_succ', map_add, map_sub, map_mul, map_ofNat,
        ratFuncEvalGerm_pureJCoefficient, hS]
      rfl
  have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
  have hslit : ∀ᶠ z in 𝓝 (0 : ℂ), 1 - z ∈ Complex.slitPlane := by
    have hc : Continuous (fun z : ℂ => 1 - z) := continuous_const.sub continuous_id
    exact hc.continuousAt.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds (by simp))
  have hC : C = 0 := eq_zero_of_ratFunc_pureFour_relation C (by
    filter_upwards [hF, hrel, eventuallyEq_deriv_of_punctured hrel, hCv,
      eventually_all.mpr (fun i => eventually_ne_zero_polynomial_eval (R i).denom_ne_zero 0),
      hn.filter_mono nhdsWithin_le_nhds, hslit.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hFz hrelz hder hcz hden hzn hs hz0
    have hR (i : Fin 4) := hasDerivAt_ratFunc_eval (R i) (hden i)
    have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; simp [h] at hzn)
    have hL : HasDerivAt (fun w : ℂ => Complex.log (1 - w))
        (2 * (1 / (2 * (z - 1)))) z := by
      have h := ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).clog hs
      convert h using 1
      simp only [Pi.sub_apply, id_eq, zero_sub]
      field_simp [hz1, sub_ne_zero.mpr (sub_ne_zero.mp hz1).symm] <;> ring
    have hD : HasDerivAt pureDilogarithm (-Complex.log (1 - z) / z) z := by
      have h := hasDerivAt_pureDilogarithm hzn
      rw [dslope_of_ne _ hz0] at h
      simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
    have hd := (((hR 0).fun_add ((hR 1).fun_mul hL)).fun_add
      ((hR 2).fun_mul (hL.fun_pow 2))).fun_add ((hR 3).fun_mul hD)
    rw [hFz.deriv, hd.deriv, hrelz] at hder
    simp only [hcz, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, div_eq_mul_inv] at hder ⊢
    linear_combination -hder)
  have hR2 : R 2 = 0 := eq_zero_of_ratFuncDerivative_eq_pureJCoefficient_mul _
    (sub_eq_zero.mp (by simpa [C] using congrFun hC 2))
  have hR3 : R 3 = 0 := eq_zero_of_ratFuncDerivative_eq_pureJCoefficient_mul _
    (sub_eq_zero.mp (by simpa [C] using congrFun hC 3))
  have h1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv (fun w => (R 1).eval (RingHom.id ℂ) w) z -
        (1 / (2 * (z - 1))) * (R 1).eval (RingHom.id ℂ) z + 1 / z = 0 := by
    have hδ := Germ.coe_eq.mp (ratFuncEvalGerm_derivative (R 1) 0)
    have hz : C 1 = 0 := congrFun hC 1
    filter_upwards [hCv, hδ] with z he hd
    have h := he 1
    simpa [hz, hR2, hR3, hd] using h.symm
  have hk : AnalyticAt ℂ (fun z : ℂ => 1 / (2 * (z - 1))) 0 :=
    analyticAt_const.div (analyticAt_const.mul (analyticAt_id.sub analyticAt_const))
      (by norm_num)
  obtain ⟨_, _, _, hzero⟩ := exists_analyticAt_eventuallyEq_of_analytic_mul_deriv_sub
    (g := fun _ => -1) (meromorphicAt_ratFunc_eval (R 1) 0) hk analyticAt_const (by
      filter_upwards [h1, self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := hz0
      simp only [sub_zero]
      have hm := congrArg (fun v : ℂ => z * v) hz
      simp only [mul_add, mul_one_div, div_self hz0', mul_zero] at hm
      linear_combination hm)
  norm_num at hzero

/-- The normalized first five pure germs are linearly independent over C(x). -/
theorem linearIndependent_pureFiveFunctions :
    letI := (ratFuncEvalGerm 0).toModule
    LinearIndependent (RatFunc ℂ)
      ![(1 : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        ((fun z : ℂ => -Complex.log (1 - z)) : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        ((fun z : ℂ => Complex.log (1 - z) ^ 2) : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        (pureDilogarithm : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        (pureJ : Germ (𝓝[≠] (0 : ℂ)) ℂ)] := by
  letI := (ratFuncEvalGerm 0).toModule
  rw [linearIndependent_fin_succ']
  constructor
  · convert linearIndependent_pureFourFunctions using 1
    funext i
    fin_cases i <;> rfl
  · intro hspan
    obtain ⟨R, hR⟩ := (Submodule.mem_span_range_iff_exists_fun (RatFunc ℂ)).mp hspan
    apply not_jFunction_eq_ratFunc_pureFourCombination ![R 0, -R 1, R 2, R 3]
      (F := pureJ) ?_ ?_
    · have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
      have h := hasDerivAt_pureJ hz
      rw [dslope_of_ne _ hz0] at h
      simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm, sub_eq_add_neg] using h
    · apply Germ.coe_eq.mp
      let L : Germ (𝓝[≠] (0 : ℂ)) ℂ := (fun z : ℂ => Complex.log (1 - z))
      simp only [Fin.sum_univ_four] at hR
      change ratFuncEvalGerm 0 (R 0) * 1 + ratFuncEvalGerm 0 (R 1) * (-L) +
        ratFuncEvalGerm 0 (R 2) * L ^ 2 + ratFuncEvalGerm 0 (R 3) *
          (pureDilogarithm : Germ (𝓝[≠] (0 : ℂ)) ℂ) = (pureJ : Germ (𝓝[≠] (0 : ℂ)) ℂ) at hR
      change (pureJ : Germ (𝓝[≠] (0 : ℂ)) ℂ) = ratFuncEvalGerm 0 (R 0) +
        ratFuncEvalGerm 0 (-R 1) * L + ratFuncEvalGerm 0 (R 2) * L ^ 2 +
          ratFuncEvalGerm 0 (R 3) * (pureDilogarithm : Germ (𝓝[≠] (0 : ℂ)) ℂ)
      rw [map_neg]
      linear_combination hR.symm

end DirichletL
