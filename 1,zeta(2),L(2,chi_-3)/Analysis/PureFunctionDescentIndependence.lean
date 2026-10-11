import Analysis.RationalFunctionPullback
import Analysis.PureFunctionDescent
import Analysis.JFunctionDescent
import Analysis.JFunctionIndependence

/-!
Independence of B1 through B5 in CDT v2, Lemma `seven` (supplied TeX
lines 7915-7958), with the normalizations in `defB`, `defB5`, and `newfunction`.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

theorem pureB5_pullback_eq_mul_pureJ :
    (fun z : ℂ => pureB5 (mobiusCoordinate z)) =ᶠ[𝓝 0]
      (fun z => mobiusAnalyticInvolution z * pureJ z) := by
  have hy : ∀ᶠ z : ℂ in 𝓝 0, ‖mobiusCoordinate z‖ < 4 :=
    (analyticAt_mobiusCoordinate (by norm_num : (0 : ℂ) ≠ 1)).continuousAt.norm.eventually_lt_const
      (by norm_num [mobiusCoordinate])
  filter_upwards [hy, pureJ_factorial_pullback,
    eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)] with z hz hj hne
  rw [pureB5_eq_mul_quotient hz, hj, mobiusCoordinate_eq_sq_div hne]
  dsimp [mobiusAnalyticInvolution]
  ring

theorem pureB3_pullback_eq_clog_sq :
    (fun z : ℂ => pureB3 (mobiusCoordinate z)) =ᶠ[𝓝 0]
      (fun z => -Complex.log (1 - z) ^ 2 / 2) := by
  filter_upwards [two_mul_pureB3_pullback] with z hz
  linear_combination (1 / 2 : ℂ) * hz

theorem pureB4_pullback_eq_pureFour :
    (fun z : ℂ => pureB4 (mobiusCoordinate z)) =ᶠ[𝓝 0]
      (fun z => (z - mobiusAnalyticInvolution z) / 2 * Complex.log (1 - z) ^ 2 +
        2 * (z - mobiusAnalyticInvolution z) * pureDilogarithm z) := by
  filter_upwards [pureB4_pullback, pureDilogarithm_mobiusAnalyticInvolution] with z hz hw
  rw [hz, hw]
  ring

/-- The five pullbacks remain independent even over the larger scalar field C(x). -/
theorem eq_zero_of_ratFunc_pureDescent_pullback_relation (R : Fin 5 → RatFunc ℂ)
    (hrel : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      (R 0).eval (RingHom.id ℂ) z +
      (R 1).eval (RingHom.id ℂ) z * pureB2 (mobiusCoordinate z) +
      (R 2).eval (RingHom.id ℂ) z * pureB3 (mobiusCoordinate z) +
      (R 3).eval (RingHom.id ℂ) z * pureB4 (mobiusCoordinate z) +
      (R 4).eval (RingHom.id ℂ) z * pureB5 (mobiusCoordinate z) = 0) : R = 0 := by
  letI := (ratFuncEvalGerm 0).toModule
  letI : CharZero (RatFunc ℂ) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (RatFunc ℂ)).injective
  let T : RatFunc ℂ := RatFunc.X - ratFuncMobiusInvolution
  have hT : T ≠ 0 := ratFuncMobiusDifference_ne_zero
  have hc : ∀ i : Fin 5,
      (![2 * R 0 + 4 * ratFuncMobiusCoordinate * R 1, 2 * T * R 1,
        -R 2 + T * R 3, 4 * T * R 3, 2 * ratFuncMobiusInvolution * R 4] :
          Fin 5 → RatFunc ℂ) i = 0 :=
    (Fintype.linearIndependent_iff.mp linearIndependent_pureFiveFunctions) _ (by
      rw [Fin.sum_univ_succ]
      simp only [Fin.sum_univ_four]
      change ratFuncEvalGerm 0 (2 * R 0 + 4 * ratFuncMobiusCoordinate * R 1) * 1 +
        (ratFuncEvalGerm 0 (2 * T * R 1) *
          ((fun z : ℂ => -Complex.log (1 - z)) : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
        ratFuncEvalGerm 0 (-R 2 + T * R 3) *
          ((fun z : ℂ => Complex.log (1 - z) ^ 2) : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
        ratFuncEvalGerm 0 (4 * T * R 3) * (pureDilogarithm : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
        ratFuncEvalGerm 0 (2 * ratFuncMobiusInvolution * R 4) *
          (pureJ : Germ (𝓝[≠] (0 : ℂ)) ℂ)) = 0
      simp only [T, map_add, map_mul, map_sub, map_neg, map_ofNat,
        ratFuncEvalGerm_mobiusCoordinate, ratFuncEvalGerm_X,
        ratFuncEvalGerm_mobiusInvolution]
      apply Germ.coe_eq.mpr
      filter_upwards [hrel, pureB2_pullback.filter_mono nhdsWithin_le_nhds,
        pureB3_pullback_eq_clog_sq.filter_mono nhdsWithin_le_nhds,
        pureB4_pullback_eq_pureFour.filter_mono nhdsWithin_le_nhds,
        pureB5_pullback_eq_mul_pureJ.filter_mono nhdsWithin_le_nhds] with z hz h2 h3 h4 h5
      rw [h2, h3, h4, h5] at hz
      change (2 * (R 0).eval (RingHom.id ℂ) z +
          4 * mobiusCoordinate z * (R 1).eval (RingHom.id ℂ) z) * 1 +
        (2 * (z - mobiusAnalyticInvolution z) * (R 1).eval (RingHom.id ℂ) z *
          (-Complex.log (1 - z)) +
        (-(R 2).eval (RingHom.id ℂ) z + (z - mobiusAnalyticInvolution z) *
          (R 3).eval (RingHom.id ℂ) z) * Complex.log (1 - z) ^ 2 +
        4 * (z - mobiusAnalyticInvolution z) * (R 3).eval (RingHom.id ℂ) z * pureDilogarithm z +
        2 * mobiusAnalyticInvolution z * (R 4).eval (RingHom.id ℂ) z * pureJ z) = 0
      linear_combination (2 : ℂ) * hz)
  have h4 : R 4 = 0 := (mul_eq_zero.mp (hc 4)).resolve_left
    (mul_ne_zero (by norm_num) ratFuncMobiusInvolution_ne_zero)
  have h3 : R 3 = 0 := (mul_eq_zero.mp (hc 3)).resolve_left (mul_ne_zero (by norm_num) hT)
  have h2 : R 2 = 0 := by
    have h : -R 2 + T * R 3 = 0 := hc 2
    simpa only [h3, mul_zero, add_zero, neg_eq_zero] using h
  have h1 : R 1 = 0 := (mul_eq_zero.mp (hc 1)).resolve_left (mul_ne_zero (by norm_num) hT)
  have h0 : R 0 = 0 := by
    have h : 2 * R 0 + 4 * ratFuncMobiusCoordinate * R 1 = 0 := hc 0
    simp only [h1, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- Polynomial relations descend faithfully through the ramified coordinate at zero. -/
theorem eq_zero_of_polynomial_pureDescent_relation (P : Fin 5 → ℂ[X])
    (hrel : ∀ᶠ z : ℂ in 𝓝[≠] 0, (P 0).eval z + (P 1).eval z * pureB2 z +
      (P 2).eval z * pureB3 z + (P 3).eval z * pureB4 z + (P 4).eval z * pureB5 z = 0) :
    P = 0 := by
  have heval (i : Fin 5) : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      (aeval ratFuncMobiusCoordinate (P i)).eval (RingHom.id ℂ) z =
        (P i).eval (mobiusCoordinate z) :=
    Germ.coe_eq.mp (ratFuncEvalGerm_aeval_mobiusCoordinate (P i))
  have hzero : (fun i => aeval ratFuncMobiusCoordinate (P i)) = 0 :=
    eq_zero_of_ratFunc_pureDescent_pullback_relation _ (by
      filter_upwards [tendsto_mobiusCoordinate_punctured_zero.eventually hrel,
        eventually_all.mpr heval] with z hz he
      simpa only [Function.comp_apply, he] using hz)
  funext i
  apply aeval_ratFuncMobiusCoordinate_injective
  simpa only [Pi.zero_apply, map_zero] using congrFun hzero i

/-- Rational coefficients may have poles at the center of the punctured germ. -/
theorem eq_zero_of_ratFunc_pureDescent_relation (R : Fin 5 → RatFunc ℂ)
    (hrel : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      (R 0).eval (RingHom.id ℂ) z + (R 1).eval (RingHom.id ℂ) z * pureB2 z +
      (R 2).eval (RingHom.id ℂ) z * pureB3 z + (R 3).eval (RingHom.id ℂ) z * pureB4 z +
      (R 4).eval (RingHom.id ℂ) z * pureB5 z = 0) : R = 0 := by
  obtain ⟨q, hq, P, hP⟩ := exists_ratFunc_denominator R
  have heval (i : Fin 5) : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      (P i).eval z = q.eval z * (R i).eval (RingHom.id ℂ) z := by
    apply Germ.coe_eq.mp
    have he := congrArg (ratFuncEvalGerm 0) (hP i)
    simpa only [map_mul, ratFuncEvalGerm_polynomial] using he
  have hzero : P = 0 := eq_zero_of_polynomial_pureDescent_relation P (by
    filter_upwards [hrel, eventually_all.mpr heval] with z hz he
    simp only [he]
    linear_combination q.eval z * hz)
  funext i
  have he := hP i
  rw [hzero, Pi.zero_apply, map_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (RatFunc.algebraMap_ne_zero hq)

/-- The first five descents in CDT Lemma `seven` are independent over C(y). -/
theorem linearIndependent_pureFiveDescents :
    letI := (ratFuncEvalGerm 0).toModule
    LinearIndependent (RatFunc ℂ)
      ![(1 : Germ (𝓝[≠] (0 : ℂ)) ℂ), (pureB2 : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        (pureB3 : Germ (𝓝[≠] (0 : ℂ)) ℂ), (pureB4 : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        (pureB5 : Germ (𝓝[≠] (0 : ℂ)) ℂ)] := by
  letI := (ratFuncEvalGerm 0).toModule
  apply Fintype.linearIndependent_iff.mpr
  intro R hR i
  rw [Fin.sum_univ_succ] at hR
  simp only [Fin.sum_univ_four] at hR
  change ratFuncEvalGerm 0 (R 0) * 1 +
    (ratFuncEvalGerm 0 (R 1) * (pureB2 : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
    ratFuncEvalGerm 0 (R 2) * (pureB3 : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
    ratFuncEvalGerm 0 (R 3) * (pureB4 : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
    ratFuncEvalGerm 0 (R 4) * (pureB5 : Germ (𝓝[≠] (0 : ℂ)) ℂ)) = 0 at hR
  apply congrFun (eq_zero_of_ratFunc_pureDescent_relation R ?_) i
  apply Germ.coe_eq.mp
  change ratFuncEvalGerm 0 (R 0) +
    ratFuncEvalGerm 0 (R 1) * (pureB2 : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
    ratFuncEvalGerm 0 (R 2) * (pureB3 : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
    ratFuncEvalGerm 0 (R 3) * (pureB4 : Germ (𝓝[≠] (0 : ℂ)) ℂ) +
    ratFuncEvalGerm 0 (R 4) * (pureB5 : Germ (𝓝[≠] (0 : ℂ)) ℂ) = 0
  simpa only [mul_one, add_assoc] using hR

end DirichletL
