import Analysis.MobiusAnalyticInvolution
import Analysis.ZagierCompanionSystem

/-!
Paths between sheets of CDT v2's `y in x`, avoiding all fourth-order singular values.
These paths will supply the sheet-exchanging monodromy in `14functions`.
-/

namespace DirichletL

open Set Polynomial

theorem finite_fiber_mobiusCoordinate (y : ℂ) : {x | mobiusCoordinate x = y}.Finite := by
  have hp : (X ^ 2 - C y * X + C y : ℂ[X]) ≠ 0 := by
    intro he
    have h := congrArg (Polynomial.coeff (R := ℂ) · 2) he
    simp at h
  apply ((finite_singleton (1 : ℂ)).union (finite_setOf_isRoot hp)).subset
  intro x hx
  by_cases hx₁ : x = 1
  · exact Or.inl hx₁
  · apply Or.inr
    change (X ^ 2 - C y * X + C y).eval x = 0
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C]
    change mobiusCoordinate x = y at hx
    dsimp only [mobiusCoordinate] at hx
    field_simp [sub_ne_zero.mpr hx₁] at hx
    linear_combination hx

theorem finite_compl_zagierODERegularSet : zagierODERegularSetᶜ.Finite := by
  have hp : zagierODECoeff 4 ≠ 0 := by
    intro he
    change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic = 0 at he
    have h := congrArg (Polynomial.eval (1 : ℂ)) he
    norm_num [zagierSingularCubic] at h
  simpa only [zagierODERegularSet, compl_setOf, not_not, Polynomial.IsRoot] using
    finite_setOf_isRoot hp

/-- Nonpoles whose invariant coordinate is fourth-order regular. -/
def zagierPullbackRegularSet : Set ℂ := {x | x ≠ 1 ∧ mobiusCoordinate x ∈ zagierODERegularSet}

theorem finite_compl_zagierPullbackRegularSet : zagierPullbackRegularSetᶜ.Finite := by
  have hf : (⋃ y ∈ zagierODERegularSetᶜ, {x | mobiusCoordinate x = y}).Finite :=
    finite_compl_zagierODERegularSet.biUnion (fun y _ => finite_fiber_mobiusCoordinate y)
  apply ((finite_singleton (1 : ℂ)).union hf).subset
  intro x hx
  by_cases hx₁ : x = 1
  · exact Or.inl hx₁
  · apply Or.inr
    have hy : mobiusCoordinate x ∈ zagierODERegularSetᶜ := by
      intro hy
      exact hx ⟨hx₁, hy⟩
    exact mem_iUnion.mpr ⟨mobiusCoordinate x, mem_iUnion.mpr ⟨hy, rfl⟩⟩

theorem isPathConnected_zagierPullbackRegularSet : IsPathConnected zagierPullbackRegularSet := by
  simpa only [compl_compl] using
    finite_compl_zagierPullbackRegularSet.countable.isPathConnected_compl_of_one_lt_rank
      (by simp [Complex.rank_real_complex])

theorem exists_zagierSheetPath {x : ℂ} (hx : x ≠ 1)
    (hreg : mobiusCoordinate x ∈ zagierODERegularSet) :
    ∃ δ : Path x (mobiusAnalyticInvolution x), (∀ t, δ t ≠ 1) ∧
      (∀ t, mobiusCoordinate (δ t) ∈ zagierODERegularSet) := by
  have hw : mobiusAnalyticInvolution x ∈ zagierPullbackRegularSet :=
    ⟨mobiusAnalyticInvolution_ne_one hx, by
      simpa only [mobiusCoordinate_mobiusAnalyticInvolution hx] using hreg⟩
  obtain ⟨δ, hδ⟩ := isPathConnected_zagierPullbackRegularSet.joinedIn
    x ⟨hx, hreg⟩ (mobiusAnalyticInvolution x) hw
  exact ⟨δ, fun t => (hδ t).1, fun t => (hδ t).2⟩

end DirichletL
