import Mathlib

/-!
The first dependence of derivative rows in the regular-system specialization
of CDT v2 `lem_Shidlovsky`, supplied TeX 2910-2935. Meanings, native
interfaces, and edge checks are recorded before the proof in
-/

namespace DirichletL

theorem exists_first_linear_dependence {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (v : ℕ → V) (hv : v 0 ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ r ≤ Module.finrank K V ∧
      LinearIndependent K (fun i : Fin r => v i.val) ∧
      v r ∈ Submodule.span K (Set.range (fun i : Fin r => v i.val)) := by
  classical
  have hex : ∃ n : ℕ, ¬ LinearIndependent K (fun i : Fin (n + 1) => v i.val) := by
    refine ⟨Module.finrank K V, ?_⟩
    intro h
    have hc := h.fintype_card_le_finrank
    simp only [Fintype.card_fin] at hc
    omega
  let r := Nat.find hex
  have hLI : LinearIndependent K (fun i : Fin r => v i.val) := by
    cases hr : r with
    | zero => exact linearIndependent_empty_type
    | succ k =>
      have hk : k < Nat.find hex := by change k < r; omega
      exact not_not.mp (Nat.find_min hex hk)
  have hfail := Nat.find_spec hex
  rw [linearIndependent_fin_succ'] at hfail
  change ¬ (LinearIndependent K (fun i : Fin r => v i.val) ∧
    v r ∉ Submodule.span K (Set.range (fun i : Fin r => v i.val))) at hfail
  have hmem : v r ∈ Submodule.span K (Set.range (fun i : Fin r => v i.val)) :=
    not_not.mp (fun h => hfail ⟨hLI, h⟩)
  have hr : 0 < r := by
    by_contra! h
    have hz : r = 0 := Nat.eq_zero_of_le_zero h
    have hs : Set.range (fun i : Fin r => v i.val) = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      rintro x ⟨i, _⟩
      have hi := i.isLt
      omega
    rw [hs, Submodule.span_empty, Submodule.mem_bot] at hmem
    apply hv
    simpa [hz] using hmem
  refine ⟨r, hr, ?_, hLI, hmem⟩
  simpa only [Fintype.card_fin] using hLI.fintype_card_le_finrank

end DirichletL
