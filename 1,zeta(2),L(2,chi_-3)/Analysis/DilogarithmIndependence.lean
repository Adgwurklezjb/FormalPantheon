import Analysis.Dilogarithm
import Analysis.LogarithmIndependence
import Analysis.MeromorphicPrimitives

/-!
The first four pure functions in CDT v2, `sec:pureX2` and Lemma `seven`
(supplied TeX lines 7311-7325 and 7915-7958). The differential proof of
the dilogarithm obstruction is recorded in the accompanying mathematical note.
-/

namespace DirichletL

open Polynomial Filter Set
open scoped Topology

/-- A dilogarithmic primitive is outside the rational span of the logarithmic functions. -/
theorem not_dilogarithmicPrimitive_eq_ratFunc_logarithmicCombination
    (R : Fin 3 → RatFunc ℂ) {F : ℂ → ℂ}
    (hF : ∀ᶠ z in 𝓝[≠] (0 : ℂ), HasDerivAt F (-Complex.log (1 - z) / z) z) :
    ¬ F =ᶠ[𝓝[≠] 0] (fun z => (R 0).eval (RingHom.id ℂ) z +
      (R 1).eval (RingHom.id ℂ) z * Complex.log (1 - z) +
      (R 2).eval (RingHom.id ℂ) z * Complex.log (1 - z) ^ 2) := by
  intro hrel
  let T : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) (-1) /
    algebraMap ℂ[X] (RatFunc ℂ) (1 - X)
  let S : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) 1 /
    algebraMap ℂ[X] (RatFunc ℂ) X
  have hT : ratFuncEvalGerm 0 T =
      ((fun z : ℂ => -1 / (1 - z)) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
    have hq : (1 - X : ℂ[X]) ≠ 0 := by
      intro h
      have hc := congrArg (fun p : ℂ[X] => p.coeff 1) h
      norm_num [coeff_one] at hc
    simpa only [eval_neg, eval_one, eval_sub, eval_X] using
      ratFuncEvalGerm_polynomial_div (-1) hq 0
  have hS : ratFuncEvalGerm 0 S =
      ((fun z : ℂ => 1 / z) : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
    simpa only [eval_one, eval_X] using
      ratFuncEvalGerm_polynomial_div 1 (X_ne_zero : (X : ℂ[X]) ≠ 0) 0
  let C : Fin 3 → RatFunc ℂ :=
    ![ratFuncDerivative (R 0) + R 1 * T,
      ratFuncDerivative (R 1) + 2 * R 2 * T + S, ratFuncDerivative (R 2)]
  have hC0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (C 0).eval (RingHom.id ℂ) z =
      (ratFuncDerivative (R 0)).eval (RingHom.id ℂ) z +
        (R 1).eval (RingHom.id ℂ) z * (-1 / (1 - z)) := by
    apply Germ.coe_eq.mp
    change ratFuncEvalGerm 0 (ratFuncDerivative (R 0) + R 1 * T) = _
    rw [map_add, map_mul, hT]
    rfl
  have hC1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (C 1).eval (RingHom.id ℂ) z =
      (ratFuncDerivative (R 1)).eval (RingHom.id ℂ) z +
        2 * (R 2).eval (RingHom.id ℂ) z * (-1 / (1 - z)) + 1 / z := by
    apply Germ.coe_eq.mp
    change ratFuncEvalGerm 0 (ratFuncDerivative (R 1) + 2 * R 2 * T + S) = _
    simp only [map_add, map_mul, map_ofNat, hT, hS]
    rfl
  have hslit : ∀ᶠ z in 𝓝 (0 : ℂ), 1 - z ∈ Complex.slitPlane := by
    have hc : Continuous (fun z : ℂ => 1 - z) := continuous_const.sub continuous_id
    exact hc.continuousAt.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds (by simp))
  have hC : C = 0 := eq_zero_of_ratFunc_clog_one_sub_relation C (by
    filter_upwards [hF, eventuallyEq_deriv_of_punctured hrel, hC0, hC1,
      eventually_all.mpr (fun i => eventually_ne_zero_polynomial_eval (R i).denom_ne_zero 0),
      hslit.filter_mono nhdsWithin_le_nhds] with z hFz hder h0 h1 hden hs
    have hR (i : Fin 3) := hasDerivAt_ratFunc_eval (R i) (hden i)
    have hL : HasDerivAt (fun w : ℂ => Complex.log (1 - w)) (-1 / (1 - z)) z := by
      simpa only [zero_sub] using
        ((hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)).clog hs
    have hd := ((hR 0).fun_add ((hR 1).fun_mul hL)).fun_add
      ((hR 2).fun_mul (hL.fun_pow 2))
    rw [hFz.deriv, hd.deriv] at hder
    simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      mul_one, h0, h1]
    change _ + _ + (ratFuncDerivative (R 2)).eval (RingHom.id ℂ) z *
      Complex.log (1 - z) ^ 2 = 0
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, div_eq_mul_inv] at hder ⊢
    linear_combination -hder)
  have h2 : ratFuncDerivative (R 2) = 0 := by simpa [C] using congrFun hC 2
  have hd2 : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv (fun w => (R 2).eval (RingHom.id ℂ) w) z = 0 := by
    apply Germ.coe_eq.mp
    change ((fun z => deriv (fun w => (R 2).eval (RingHom.id ℂ) w) z) :
      Germ (𝓝[≠] (0 : ℂ)) ℂ) = 0
    rw [← ratFuncEvalGerm_derivative, h2, map_zero]
  obtain ⟨u, hu, hRu, _⟩ := exists_analyticAt_eventuallyEq_of_analytic_mul_deriv
    (g := fun _ => 0) (meromorphicAt_ratFunc_eval (R 2) 0) analyticAt_const (by
      filter_upwards [hd2] with z hz
      simp [hz])
  have h1 : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv (fun w => (R 1).eval (RingHom.id ℂ) w) z +
        2 * u z * (-1 / (1 - z)) + 1 / z = 0 := by
    have hδ := Germ.coe_eq.mp (ratFuncEvalGerm_derivative (R 1) 0)
    have hzero : C 1 = 0 := congrFun hC 1
    filter_upwards [hC1, hδ, hRu] with z hz hd hu
    simpa only [hzero, RatFunc.eval_zero, hd, hu] using hz.symm
  let g : ℂ → ℂ := fun z => 2 * z * u z / (1 - z) - 1
  have hg : AnalyticAt ℂ g 0 :=
    (((analyticAt_const.mul analyticAt_id).mul hu).div
      (analyticAt_const.sub analyticAt_id) (by norm_num)).sub analyticAt_const
  obtain ⟨_, _, _, hzero⟩ := exists_analyticAt_eventuallyEq_of_analytic_mul_deriv
    (meromorphicAt_ratFunc_eval (R 1) 0) hg (by
      filter_upwards [h1, self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := hz0
      dsimp [g]
      simp only [sub_zero, div_eq_mul_inv] at hz ⊢
      linear_combination (norm := ring_nf) z * hz
      simp [hz0'])
  norm_num [g] at hzero

/-- The exact first four pure functions of CDT are independent over C(x). -/
theorem linearIndependent_pureFourFunctions :
    letI := (ratFuncEvalGerm 0).toModule
    LinearIndependent (RatFunc ℂ)
      ![(1 : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        ((fun z : ℂ => -Complex.log (1 - z)) : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        ((fun z : ℂ => Complex.log (1 - z) ^ 2) : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        (pureDilogarithm : Germ (𝓝[≠] (0 : ℂ)) ℂ)] := by
  letI := (ratFuncEvalGerm 0).toModule
  rw [linearIndependent_fin_succ']
  constructor
  · convert linearIndependent_pureLogarithmicFunctions using 1
    funext i
    fin_cases i <;> rfl
  · intro hspan
    obtain ⟨R, hR⟩ := (Submodule.mem_span_range_iff_exists_fun (RatFunc ℂ)).mp hspan
    apply not_dilogarithmicPrimitive_eq_ratFunc_logarithmicCombination ![R 0, -R 1, R 2]
      (F := pureDilogarithm) ?_ ?_
    · have hn : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ < 1 :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds (by norm_num)
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz0
      have h := hasDerivAt_pureDilogarithm hz
      rw [dslope_of_ne _ hz0] at h
      simpa [slope, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
    · apply Germ.coe_eq.mp
      let L : Germ (𝓝[≠] (0 : ℂ)) ℂ := (fun z : ℂ => Complex.log (1 - z))
      simp only [Fin.sum_univ_three] at hR
      change ratFuncEvalGerm 0 (R 0) * 1 + ratFuncEvalGerm 0 (R 1) * (-L) +
        ratFuncEvalGerm 0 (R 2) * L ^ 2 = (pureDilogarithm : Germ (𝓝[≠] (0 : ℂ)) ℂ) at hR
      change (pureDilogarithm : Germ (𝓝[≠] (0 : ℂ)) ℂ) = ratFuncEvalGerm 0 (R 0) +
        ratFuncEvalGerm 0 (-R 1) * L + ratFuncEvalGerm 0 (R 2) * L ^ 2
      rw [map_neg]
      linear_combination hR.symm

end DirichletL
