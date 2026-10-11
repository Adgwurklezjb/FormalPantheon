import Analysis.BlockEnumeration

/-!
The finite block reference values for CDT v2, supplied TeX 4160-4228.
The right endpoint convention and declaration meanings precede these bodies
-/

namespace DirichletL

variable {κ : Type*} [DecidableEq κ] {d : ℕ}

/-- Evaluate each block profile on its regular grid, using the original coordinate ordering. -/
noncomputable def blockGridValues (b : Fin d → κ) (f : κ → ℝ → ℝ) (j : Fin d) : ℝ :=
  let qi := (blockIndexEquiv b).symm j
  f qi.1 (((qi.2.val : ℝ) + 1) / (Finset.univ.filter (fun j => b j = qi.1)).card)

theorem blockGridValues_orderEmbOfFin (b : Fin d → κ) (f : κ → ℝ → ℝ) (q : κ)
    (i : Fin (Finset.univ.filter (fun j => b j = q)).card) :
    blockGridValues b f ((Finset.univ.filter (fun j => b j = q)).orderEmbOfFin rfl i) =
      f q (((i.val : ℝ) + 1) / (Finset.univ.filter (fun j => b j = q)).card) := by
  rw [← blockIndexEquiv_apply]
  exact congrArg
    (fun qi : Σ q, Fin (Finset.univ.filter (fun j => b j = q)).card =>
      f qi.1 (((qi.2.val : ℝ) + 1) / (Finset.univ.filter (fun j => b j = qi.1)).card))
    ((blockIndexEquiv b).symm_apply_apply ⟨q, i⟩)

theorem abs_blockGridValues_le (b : Fin d → κ) (f : κ → ℝ → ℝ) {B : ℝ}
    (hB : ∀ q u, u ∈ Set.Icc (0 : ℝ) 1 → |f q u| ≤ B) (j : Fin d) :
    |blockGridValues b f j| ≤ B := by
  obtain ⟨⟨q, i⟩, rfl⟩ := (blockIndexEquiv b).surjective j
  rw [blockIndexEquiv_apply, blockGridValues_orderEmbOfFin]
  apply hB
  have hn : 0 < ((Finset.univ.filter (fun j => b j = q)).card : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  refine ⟨by positivity, (div_le_one hn).mpr ?_⟩
  exact_mod_cast (Nat.succ_le_of_lt i.isLt)

end DirichletL
