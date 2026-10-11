import Analysis.PureFunctionPrimitiveIndependence
import Analysis.PureFunctionIntegrals

/-!
Rational independence of the seven pure functions in CDT v2, Lemma `seven`
(supplied TeX lines 7915-8015), with the normalized integrals in `defB67`.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

/-- CDT's seven pure functions, in paper order. -/
noncomputable def pureSevenDescentFamily : Fin 7 → ℂ → ℂ :=
  Fin.append pureFiveDescentFamily ![pureB6, pureB7]

theorem eventually_hasDerivAt_pureIntegralFamily (j : Fin 2) :
    ∀ᶠ z : ℂ in 𝓝[≠] 0,
      HasDerivAt (![pureB6, pureB7] j) (![pureB3, pureB4] j z / z) z := by
  fin_cases j
  · have ha := analyticAt_pureB6 (by norm_num : ‖(0 : ℂ)‖ < 4)
    filter_upwards [ha.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      pureB6_deriv] with z hz hd
    change HasDerivAt pureB6 (pureB3 z / z) z
    rw [← hd]
    exact hz.differentiableAt.hasDerivAt
  · filter_upwards [analyticAt_pureB7.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      pureB7_deriv] with z hz hd
    change HasDerivAt pureB7 (pureB4 z / z) z
    rw [← hd]
    exact hz.differentiableAt.hasDerivAt

theorem eq_zero_of_pureSevenDescentFamilyRelation (C : Fin 7 → RatFunc ℂ)
    (hrel : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      ∑ k, (C k).eval (RingHom.id ℂ) z * pureSevenDescentFamily k z = 0) : C = 0 := by
  have hneg (i : Fin 5) := Germ.coe_eq.mp (map_neg (ratFuncEvalGerm 0) (C (i.castAdd 2)))
  obtain ⟨hA, hR⟩ := eq_zero_of_pureRatFuncPrimitiveRelation
    (fun j => C (j.natAdd 5)) (fun i => -C (i.castAdd 2)) ![pureB6, pureB7]
    eventually_hasDerivAt_pureIntegralFamily (by
      filter_upwards [hrel, eventually_all.mpr hneg] with z hz hnegz
      rw [Fin.sum_univ_add (a := 5) (b := 2)] at hz
      simp only [pureSevenDescentFamily, Fin.append_left, Fin.append_right] at hz
      simp only [hnegz, Function.comp_apply, neg_mul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_right hz)
  funext k
  refine Fin.addCases (m := 5) (n := 2) ?_ ?_ k
  · intro i
    exact neg_eq_zero.mp (congrFun hR i)
  · intro j
    exact congrFun hA j

/-- The literal seven-vector of punctured germs is independent over C(y). -/
theorem linearIndependent_pureSevenDescents :
    letI := (ratFuncEvalGerm 0).toModule
    LinearIndependent (RatFunc ℂ)
      ![(1 : Germ (𝓝[≠] (0 : ℂ)) ℂ), (pureB2 : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        (pureB3 : Germ (𝓝[≠] (0 : ℂ)) ℂ), (pureB4 : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        (pureB5 : Germ (𝓝[≠] (0 : ℂ)) ℂ), (pureB6 : Germ (𝓝[≠] (0 : ℂ)) ℂ),
        (pureB7 : Germ (𝓝[≠] (0 : ℂ)) ℂ)] := by
  letI := (ratFuncEvalGerm 0).toModule
  have h : LinearIndependent (RatFunc ℂ)
      (fun k => (pureSevenDescentFamily k : Germ (𝓝[≠] (0 : ℂ)) ℂ)) := by
    apply Fintype.linearIndependent_iff.mpr
    intro C hC i
    change ∑ k, ratFuncEvalGerm 0 (C k) *
      (pureSevenDescentFamily k : Germ (𝓝[≠] (0 : ℂ)) ℂ) = 0 at hC
    have he : ((fun z => ∑ k, (C k).eval (RingHom.id ℂ) z * pureSevenDescentFamily k z) :
        Germ (𝓝[≠] (0 : ℂ)) ℂ) =
        ∑ k, ratFuncEvalGerm 0 (C k) * (pureSevenDescentFamily k : Germ (𝓝[≠] (0 : ℂ)) ℂ) := by
      rw [show (fun z => ∑ k, (C k).eval (RingHom.id ℂ) z * pureSevenDescentFamily k z) =
          ∑ k, (fun z => (C k).eval (RingHom.id ℂ) z * pureSevenDescentFamily k z) by
        funext z
        simp only [Finset.sum_apply]]
      rw [Germ.coe_sum]
      rfl
    exact congrFun (eq_zero_of_pureSevenDescentFamilyRelation C
      (Germ.coe_eq.mp (he.trans hC))) i
  convert h using 1
  funext i
  fin_cases i <;> rfl

end DirichletL
