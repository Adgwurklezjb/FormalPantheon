import Analysis.PureFunctionRelations
import Analysis.PureFunctionRational

/-!
Polynomial-degree reduction and rational denominator clearing for CDT v2,
Lemma `seven`, equations `lasttwo` and `lasttwotwo` (supplied TeX lines 7955-8015).
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

/-- Polynomial primitive coefficients and unrestricted rational first-five coefficients vanish. -/
theorem eq_zero_of_purePolynomialPrimitiveRelation (P : Fin 2 → ℂ[X]) (R : Fin 5 → RatFunc ℂ)
    (J : Fin 2 → ℂ → ℂ)
    (hJ : ∀ j, ∀ᶠ z : ℂ in 𝓝[≠] 0, HasDerivAt (J j) (![pureB3, pureB4] j z / z) z)
    (hrel : (fun z => ∑ j, (P j).eval z * J j z) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z => ∑ i, (R i).eval (RingHom.id ℂ) z * pureFiveDescentFamily i z) :
    P = 0 ∧ R = 0 := by
  letI : CharZero (RatFunc ℂ) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (RatFunc ℂ)).injective
  have hx4 : (4 : RatFunc ℂ) - RatFunc.X ≠ 0 := by
    have hp : (4 - X : ℂ[X]) ≠ 0 := by
      intro h
      have he := congrArg (fun p : ℂ[X] => p.eval 0) h
      norm_num at he
    simpa only [map_sub, map_ofNat, RatFunc.algebraMap_X] using RatFunc.algebraMap_ne_zero hp
  have hconstant (Q : Fin 2 → ℂ[X]) (B : Fin 5 → RatFunc ℂ)
      (hQ : ∀ j, (Q j).derivative = 0)
      (hrel : (fun z => ∑ j, (Q j).eval z * J j z) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun z => ∑ i, (B i).eval (RingHom.id ℂ) z * pureFiveDescentFamily i z) :
      Q = 0 ∧ B = 0 := by
    have hpoly (j : Fin 2) := eq_C_of_derivative_eq_zero (hQ j)
    have hstep : purePrimitiveRelationStep Q B = 0 :=
      eq_zero_of_pureFiveDescentFamilyRelation _ (by
        filter_upwards [purePrimitiveRelation_deriv Q B J hJ hrel] with z hz
        simpa only [hQ, eval_zero, zero_mul, Finset.sum_const_zero, eq_comm] using hz)
    have h2 : ratFuncDerivative (B 2) - algebraMap ℂ[X] (RatFunc ℂ) (Q 0) / RatFunc.X = 0 := by
      simpa [purePrimitiveRelationStep] using congrFun hstep 2
    have ha : (Q 0).coeff 0 = 0 := eq_zero_of_X_mul_ratFuncDerivative_eq (B 2) _ (by
      rw [hpoly 0] at h2
      linear_combination (norm := skip) RatFunc.X * h2
      simp only [RatFunc.algebraMap_C, RatFunc.C]
      field_simp [RatFunc.X_ne_zero]
      ring)
    have h3 : ratFuncDerivative (B 3) + pureDerivativeInverse * 2 * (2 - RatFunc.X) * B 3 -
        algebraMap ℂ[X] (RatFunc ℂ) (Q 1) / RatFunc.X = 0 := by
      simpa [purePrimitiveRelationStep] using congrFun hstep 3
    have hb : (Q 1).coeff 0 = 0 := eq_zero_of_ratFunc_pureB4_primitive_ode (B 3) _ (by
      rw [hpoly 1] at h3
      linear_combination (norm := skip) (RatFunc.X * (4 - RatFunc.X)) * h3
      simp only [pureDerivativeInverse, map_mul, map_sub, map_one, map_ofNat,
        RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.C]
      field_simp [RatFunc.X_ne_zero, hx4]
      ring)
    have hQzero : Q = 0 := by
      funext j
      fin_cases j
      · change Q 0 = 0
        rw [hpoly 0, ha, map_zero]
      · change Q 1 = 0
        rw [hpoly 1, hb, map_zero]
    refine ⟨hQzero, eq_zero_of_pureFiveDescentFamilyRelation B ?_⟩
    filter_upwards [hrel] with z hz
    simpa only [hQzero, Pi.zero_apply, eval_zero, zero_mul, Finset.sum_const_zero, eq_comm] using hz
  have h (n : ℕ) : ∀ Q : Fin 2 → ℂ[X], (∀ j, (Q j).natDegree ≤ n) →
      ∀ B : Fin 5 → RatFunc ℂ,
      ((fun z => ∑ j, (Q j).eval z * J j z) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun z => ∑ i, (B i).eval (RingHom.id ℂ) z * pureFiveDescentFamily i z) →
        Q = 0 ∧ B = 0 := by
    induction n with
    | zero =>
      intro Q hn B hrel
      exact hconstant Q B
        (fun j => derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero (hn j))) hrel
    | succ n ih =>
      intro Q hn B hrel
      obtain ⟨hQ, _⟩ := ih (fun j => (Q j).derivative)
        (fun j => (natDegree_derivative_le _).trans (by have := hn j; omega))
        (purePrimitiveRelationStep Q B) (purePrimitiveRelation_deriv Q B J hJ hrel)
      exact hconstant Q B (fun j => congrFun hQ j) hrel
  exact h (Finset.univ.sup fun j => (P j).natDegree) P
    (fun j => Finset.le_sup (f := fun j => (P j).natDegree) (Finset.mem_univ j)) R hrel

/-- Arbitrary rational coefficients in a relation involving the two primitives vanish. -/
theorem eq_zero_of_pureRatFuncPrimitiveRelation (A : Fin 2 → RatFunc ℂ) (R : Fin 5 → RatFunc ℂ)
    (J : Fin 2 → ℂ → ℂ)
    (hJ : ∀ j, ∀ᶠ z : ℂ in 𝓝[≠] 0, HasDerivAt (J j) (![pureB3, pureB4] j z / z) z)
    (hrel : (fun z => ∑ j, (A j).eval (RingHom.id ℂ) z * J j z) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun z => ∑ i, (R i).eval (RingHom.id ℂ) z * pureFiveDescentFamily i z) :
    A = 0 ∧ R = 0 := by
  obtain ⟨q, hq, P, hP⟩ := exists_ratFunc_denominator A
  let B : Fin 5 → RatFunc ℂ := fun i => algebraMap ℂ[X] (RatFunc ℂ) q * R i
  have hPeval (j : Fin 2) : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      (P j).eval z = q.eval z * (A j).eval (RingHom.id ℂ) z := by
    apply Germ.coe_eq.mp
    have he := congrArg (ratFuncEvalGerm 0) (hP j)
    simpa only [map_mul, ratFuncEvalGerm_polynomial] using he
  have hBeval (i : Fin 5) : ∀ᶠ z : ℂ in 𝓝[≠] 0,
      (B i).eval (RingHom.id ℂ) z = q.eval z * (R i).eval (RingHom.id ℂ) z := by
    apply Germ.coe_eq.mp
    change ratFuncEvalGerm 0 (algebraMap ℂ[X] (RatFunc ℂ) q * R i) = _
    rw [map_mul, ratFuncEvalGerm_polynomial]
    rfl
  obtain ⟨hPzero, hBzero⟩ := eq_zero_of_purePolynomialPrimitiveRelation P B J hJ (by
    filter_upwards [hrel, eventually_all.mpr hPeval, eventually_all.mpr hBeval] with z hz hPz hBz
    simp only [hPz, hBz, mul_assoc, ← Finset.mul_sum]
    exact congrArg (fun t : ℂ => q.eval z * t) hz)
  constructor
  · funext j
    have he := hP j
    rw [hPzero, Pi.zero_apply, map_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (RatFunc.algebraMap_ne_zero hq)
  · funext i
    have he : algebraMap ℂ[X] (RatFunc ℂ) q * R i = 0 := congrFun hBzero i
    exact (mul_eq_zero.mp he).resolve_left (RatFunc.algebraMap_ne_zero hq)

end DirichletL
