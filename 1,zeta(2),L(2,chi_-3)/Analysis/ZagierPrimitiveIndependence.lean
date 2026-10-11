import Analysis.ZagierPrimitiveNormalization

/-!
Rational independence of the homogeneous seven-function family in CDT v2,
`14functions`, before `todiff` (supplied TeX lines 8087-8115).
-/

namespace DirichletL

open Polynomial Filter Set
open scoped Topology

/-- Arbitrary rational primitive and derivative coefficients in a relation vanish. -/
theorem eq_zero_of_zagierRatFuncPrimitiveRelation {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (A : Fin 3 → RatFunc ℂ) (B : Fin 4 → RatFunc ℂ)
    {φ : zagierSolutionGerms (mobiusCoordinate r)} (hφ : φ ≠ 0) {f : ℂ → ℂ}
    (hrep : (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f)
    (J : Fin 3 → ℂ → ℂ)
    (hJ : ∀ j, ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r), HasDerivAt (J j) (f z / z ^ (j : ℕ)) z)
    (hrel : (fun z => ∑ j, (A j).eval (RingHom.id ℂ) z * J j z) =ᶠ[𝓝[≠] (mobiusCoordinate r)]
      fun z => ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState f z i) :
    A = 0 ∧ B = 0 := by
  let R : Fin 3 ⊕ Fin 4 → RatFunc ℂ := Sum.elim A B
  obtain ⟨q, hq, P, hP⟩ := exists_ratFunc_denominator R
  have hG (p : ℂ[X]) : ratFuncEvalGerm (mobiusCoordinate r) (algebraMap ℂ[X] (RatFunc ℂ) p) =
      (fun z => p.eval z : ℂ → ℂ) := by
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall (fun z => by
      simp only [RatFunc.eval_algebraMap, Algebra.algebraMap_self_apply, Polynomial.eval₂_id])
  have heval (k : Fin 3 ⊕ Fin 4) : ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r),
      (P k).eval z = q.eval z * (R k).eval (RingHom.id ℂ) z := by
    apply Germ.coe_eq.mp
    have he := congrArg (ratFuncEvalGerm (mobiusCoordinate r)) (hP k)
    simpa only [map_mul (ratFuncEvalGerm (mobiusCoordinate r)), hG] using he
  let C : Fin 4 → RatFunc ℂ := fun i => algebraMap ℂ[X] (RatFunc ℂ) (P (Sum.inr i))
  have hCval (i : Fin 4) (z : ℂ) : (C i).eval (RingHom.id ℂ) z = (P (Sum.inr i)).eval z := by
    simp only [C, RatFunc.eval_algebraMap, Algebra.algebraMap_self_apply, Polynomial.eval₂_id]
  have hclear : (fun z => ∑ j, (P (Sum.inl j)).eval z * J j z) =ᶠ[𝓝[≠] (mobiusCoordinate r)]
      fun z => ∑ i, (C i).eval (RingHom.id ℂ) z * zagierODEState f z i := by
    filter_upwards [hrel, eventually_all.mpr heval] with z hz hEz
    simp only [hCval, hEz, R, Sum.elim_inl, Sum.elim_inr, mul_assoc, ← Finset.mul_sum]
    exact congrArg (fun x : ℂ => q.eval z * x) hz
  obtain ⟨hP₀, hC₀⟩ := eq_zero_of_zagierPolynomialPrimitiveRelation hr
    (fun j => P (Sum.inl j)) C (fun i => zagierRatFuncCoefficients.algebraMap_mem _)
    hφ hrep J hJ hclear
  have hPzero (k : Fin 3 ⊕ Fin 4) : algebraMap ℂ[X] (RatFunc ℂ) (P k) = 0 := by
    cases k with
    | inl j => rw [show P (Sum.inl j) = 0 from congrFun hP₀ j, map_zero]
    | inr i => exact congrFun hC₀ i
  have hRzero (k : Fin 3 ⊕ Fin 4) : R k = 0 := by
    have he : algebraMap ℂ[X] (RatFunc ℂ) q * R k = 0 := (hP k).symm.trans (hPzero k)
    exact (mul_eq_zero.mp he).resolve_left (RatFunc.algebraMap_ne_zero hq)
  exact ⟨funext (fun j => hRzero (Sum.inl j)), funext (fun i => hRzero (Sum.inr i))⟩

/-- The three primitives followed by the four derivative entries. -/
noncomputable def zagierHomogeneousPrimitiveFamily (f : ℂ → ℂ) (J : Fin 3 → ℂ → ℂ) :
    Fin 7 → ℂ → ℂ :=
  Fin.append J (fun i z => zagierODEState f z i)

theorem eq_zero_of_zagierHomogeneousFamilyRelation {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (C : Fin 7 → RatFunc ℂ)
    {φ : zagierSolutionGerms (mobiusCoordinate r)} (hφ : φ ≠ 0) {f : ℂ → ℂ}
    (hrep : (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f)
    (J : Fin 3 → ℂ → ℂ)
    (hJ : ∀ j, ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r), HasDerivAt (J j) (f z / z ^ (j : ℕ)) z)
    (hrel : ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r),
      ∑ k, (C k).eval (RingHom.id ℂ) z * zagierHomogeneousPrimitiveFamily f J k z = 0) :
    C = 0 := by
  have hneg (i : Fin 4) := Germ.coe_eq.mp
    (map_neg (ratFuncEvalGerm (mobiusCoordinate r)) (C (i.natAdd 3)))
  obtain ⟨hA, hB⟩ := eq_zero_of_zagierRatFuncPrimitiveRelation hr
    (fun j => C (j.castAdd 4)) (fun i => -C (i.natAdd 3)) hφ hrep J hJ (by
      filter_upwards [hrel, eventually_all.mpr hneg] with z hz hnegz
      rw [Fin.sum_univ_add (a := 3) (b := 4)] at hz
      simp only [zagierHomogeneousPrimitiveFamily, Fin.append_left, Fin.append_right] at hz
      simp only [hnegz, Function.comp_apply, neg_mul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left hz)
  funext k
  refine Fin.addCases (m := 3) (n := 4) ?_ ?_ k
  · intro j
    exact congrFun hA j
  · intro i
    exact neg_eq_zero.mp (congrFun hB i)

/-- Rational independence uses multiplication by rational evaluation germs as its scalar action. -/
theorem linearIndependent_zagierHomogeneousPrimitiveFamily {r : ℝ}
    (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    {φ : zagierSolutionGerms (mobiusCoordinate r)} (hφ : φ ≠ 0) {f : ℂ → ℂ}
    (hrep : (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f)
    (J : Fin 3 → ℂ → ℂ)
    (hJ : ∀ j, ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r), HasDerivAt (J j) (f z / z ^ (j : ℕ)) z) :
    letI := (ratFuncEvalGerm (mobiusCoordinate r)).toModule
    LinearIndependent (RatFunc ℂ) (fun k : Fin 7 =>
      (zagierHomogeneousPrimitiveFamily f J k : Germ (𝓝[≠] (mobiusCoordinate r)) ℂ)) := by
  letI := (ratFuncEvalGerm (mobiusCoordinate r)).toModule
  apply Fintype.linearIndependent_iff.mpr
  intro C hC i
  change ∑ k, ratFuncEvalGerm (mobiusCoordinate r) (C k) *
    (zagierHomogeneousPrimitiveFamily f J k : Germ (𝓝[≠] (mobiusCoordinate r)) ℂ) = 0 at hC
  have he : ((fun z => ∑ k, (C k).eval (RingHom.id ℂ) z *
      zagierHomogeneousPrimitiveFamily f J k z) : Germ (𝓝[≠] (mobiusCoordinate r)) ℂ) =
      ∑ k, ratFuncEvalGerm (mobiusCoordinate r) (C k) *
        (zagierHomogeneousPrimitiveFamily f J k : Germ (𝓝[≠] (mobiusCoordinate r)) ℂ) := by
    rw [show (fun z => ∑ k, (C k).eval (RingHom.id ℂ) z *
      zagierHomogeneousPrimitiveFamily f J k z) =
        ∑ k, (fun z => (C k).eval (RingHom.id ℂ) z * zagierHomogeneousPrimitiveFamily f J k z) by
      funext z
      simp only [Finset.sum_apply]]
    rw [Germ.coe_sum]
    rfl
  exact congrFun (eq_zero_of_zagierHomogeneousFamilyRelation hr C hφ hrep J hJ
    (Germ.coe_eq.mp (he.trans hC))) i

end DirichletL
