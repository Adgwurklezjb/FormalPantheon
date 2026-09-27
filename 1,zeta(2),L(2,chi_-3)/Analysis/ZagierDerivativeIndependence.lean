import Analysis.ZagierMonodromyIrreducibility
import Analysis.ZagierRationalRelations

/-!
Rational derivative independence for G_A in CDT v2, `14functions`, after `todiff`.
The actual full-orbit theorem supplies the irreducibility criterion at interval bases.
-/

namespace DirichletL

open Filter Set
open scoped Topology

/-- Actual monodromy at an interval base has no proper nonzero invariant subspace. -/
theorem isSimpleOrder_zagierMonodromy {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ)) :
    IsSimpleOrder (zagierMonodromyRepresentation
      ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩).invtSubmodule := by
  letI : Nontrivial (zagierSolutionGerms (mobiusCoordinate r)) :=
    (zagierSolutionGermStateEquiv (mobiusCoordinate_regular_of_mem_Ioo hr)).symm.injective.nontrivial
  refine { eq_bot_or_eq_top := ?_ }
  intro W
  by_cases hW : W.val = ⊥
  · exact Or.inl (Subtype.ext hW)
  · apply Or.inr
    obtain ⟨φ, hφ, hne⟩ := W.val.ne_bot_iff.mp hW
    apply Subtype.ext
    apply top_unique
    rw [← zagierMonodromyOrbitSpan_eq_top hr hne]
    exact zagierMonodromyOrbitSpan_le _ W.property hφ

theorem eq_zero_of_zagierPolynomialRelation {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (P : Fin 4 → Polynomial ℂ) {φ : zagierSolutionGerms (mobiusCoordinate r)} (hφ : φ ≠ 0)
    (hrel : φ ∈ zagierPolynomialRelationSubmodule P (mobiusCoordinate r)) : P = 0 :=
  eq_zero_of_zagierPolynomialRelation_of_orbitSpan_eq_top
    ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩ P hrel
    (zagierMonodromyOrbitSpan_eq_top hr hφ)

/-- Rational relations at an interval base vanish, even with coefficient poles at the base. -/
theorem eq_zero_of_zagierRatFuncRelation {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (B : Fin 4 → RatFunc ℂ) {φ : zagierSolutionGerms (mobiusCoordinate r)} (hφ : φ ≠ 0)
    {f : ℂ → ℂ} (hrep : (φ : Germ (𝓝 (mobiusCoordinate r)) ℂ) = f)
    (hrel : ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r),
      ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState f z i = 0) : B = 0 :=
  eq_zero_of_zagierRatFuncRelation_of_isSimpleOrder
    ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩
    (isSimpleOrder_zagierMonodromy hr) B hφ hrep hrel

/-- The first four derivatives of actual G_A have no nonzero rational coefficient relation. -/
theorem eq_zero_of_zagierRatFuncRelation_hA {r : ℝ} (hr : r ∈ Ioo 0 (1 / 9 : ℝ))
    (hb : ‖mobiusCoordinate r‖ < 1 / 648) (B : Fin 4 → RatFunc ℂ)
    (hrel : ∀ᶠ z in 𝓝[≠] (mobiusCoordinate r),
      ∑ i, (B i).eval (RingHom.id ℂ) z * zagierODEState (symmetrizedAnalytic hA) z i = 0) :
    B = 0 :=
  eq_zero_of_zagierRatFuncRelation_hA_of_isSimpleOrder
    ⟨mobiusCoordinate r, mobiusCoordinate_regular_of_mem_Ioo hr⟩ hb
    (isSimpleOrder_zagierMonodromy hr) B hrel

end DirichletL
