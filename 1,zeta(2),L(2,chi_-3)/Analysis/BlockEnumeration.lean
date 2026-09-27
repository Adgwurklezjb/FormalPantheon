import Comparator.Statement

/-!
Increasing block enumeration for CDT v2, supplied TeX 4069-4137 and 4160-4228.
-/

namespace DirichletL

variable {κ : Type*} [DecidableEq κ] {d : ℕ}

/-- The disjoint union of the increasing block enumerations is the original coordinate set. -/
noncomputable def blockIndexEquiv (b : Fin d → κ) :
    (Σ q, Fin (Finset.univ.filter (fun j => b j = q)).card) ≃ Fin d :=
  (Equiv.sigmaCongrRight fun q =>
    ((Finset.univ.filter (fun j => b j = q)).orderIsoOfFin rfl).toEquiv.trans
      (Equiv.subtypeEquivRight fun j => by simp)).trans (Equiv.sigmaFiberEquiv b)

theorem blockIndexEquiv_apply (b : Fin d → κ) (q : κ)
    (i : Fin (Finset.univ.filter (fun j => b j = q)).card) :
    blockIndexEquiv b ⟨q, i⟩ =
      (Finset.univ.filter (fun j => b j = q)).orderEmbOfFin rfl i := rfl

theorem blockIndexEquiv_label (b : Fin d → κ) (q : κ)
    (i : Fin (Finset.univ.filter (fun j => b j = q)).card) :
    b (blockIndexEquiv b ⟨q, i⟩) = q := by
  simpa only [blockIndexEquiv_apply, Finset.mem_filter, Finset.mem_univ, true_and] using
    (Finset.univ.filter (fun j => b j = q)).orderEmbOfFin_mem rfl i

theorem exists_perm_block_orderEmbOfFin (b : Fin d → κ)
    (σ : ∀ q, Equiv.Perm (Fin (Finset.univ.filter (fun j => b j = q)).card)) :
    ∃ τ : Equiv.Perm (Fin d),
      (∀ q i, τ ((Finset.univ.filter (fun j => b j = q)).orderEmbOfFin rfl i) =
        (Finset.univ.filter (fun j => b j = q)).orderEmbOfFin rfl (σ q i)) ∧
      ∀ j, b (τ j) = b j := by
  let E := blockIndexEquiv b
  let τ := (E.symm.trans (Equiv.Perm.sigmaCongrRight σ)).trans E
  have hτ (q : κ) (i : Fin (Finset.univ.filter (fun j => b j = q)).card) :
      τ (E ⟨q, i⟩) = E ⟨q, σ q i⟩ := by
    simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sigmaCongrRight_apply]
  refine ⟨τ, ?_, ?_⟩
  · intro q i
    exact hτ q i
  · intro j
    obtain ⟨⟨q, i⟩, rfl⟩ := E.surjective j
    rw [hτ]
    exact (blockIndexEquiv_label b q _).trans (blockIndexEquiv_label b q i).symm

end DirichletL
