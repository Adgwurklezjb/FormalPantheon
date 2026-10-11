import Analysis.ZagierPathTransport

/-!
The monodromy representation of the homogeneous Zagier equation on its regular locus.
CDT v2, Lemma `14functions`, uses the span of these translates. Irreducibility
and removal of the extra cubic punctures remain separate obligations.
-/

namespace DirichletL

attribute [local instance] Path.Homotopic.setoid

/-- Actual solution-germ transport descended to the canonical path homotopy quotient. -/
noncomputable def zagierHomotopyTransport (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (P : Path.Homotopic.Quotient x y) :
    zagierSolutionGerms (x : ℂ) ≃ₗ[ℂ] zagierSolutionGerms (y : ℂ) :=
  Quotient.lift (zagierPathTransportEquiv b)
    (fun _ _ h => zagierPathTransportEquiv_of_homotopic b h) P

@[simp]
theorem zagierHomotopyTransport_mk (b : zagierODERegularSet)
    {x y : zagierODERegularSet} (γ : Path x y) :
    zagierHomotopyTransport b ⟦γ⟧ = zagierPathTransportEquiv b γ := rfl

theorem zagierHomotopyTransport_refl (b x : zagierODERegularSet) :
    zagierHomotopyTransport b ⟦Path.refl x⟧ = LinearEquiv.refl ℂ _ := by
  apply LinearEquiv.ext
  intro φ
  exact zagierPathTransport_refl b x φ

theorem zagierHomotopyTransport_comp (b : zagierODERegularSet)
    {x y z : zagierODERegularSet} (P : Path.Homotopic.Quotient x y)
    (Q : Path.Homotopic.Quotient y z) :
    zagierHomotopyTransport b (P.comp Q) =
      (zagierHomotopyTransport b P).trans (zagierHomotopyTransport b Q) := by
  induction P, Q using Quotient.inductionOn₂ with
  | _ γ δ =>
    apply LinearEquiv.ext
    intro φ
    exact zagierPathTransport_trans b γ δ φ

/-- The fundamental group acts by the actual complex-linear continuation maps. -/
noncomputable def zagierMonodromy (b : zagierODERegularSet) :
    FundamentalGroup zagierODERegularSet b →*
      (zagierSolutionGerms (b : ℂ) ≃ₗ[ℂ] zagierSolutionGerms (b : ℂ)) where
  toFun g := zagierHomotopyTransport b g.hom
  map_one' := zagierHomotopyTransport_refl b b
  map_mul' g h := by
    change zagierHomotopyTransport b (h.hom.comp g.hom) =
      zagierHomotopyTransport b g.hom * zagierHomotopyTransport b h.hom
    rw [zagierHomotopyTransport_comp]
    rfl

@[simp]
theorem zagierMonodromy_loop (b : zagierODERegularSet) (γ : Path b b) :
    zagierMonodromy b (FundamentalGroup.fromPath (X := TopCat.of zagierODERegularSet) ⟦γ⟧) =
      zagierPathTransportEquiv b γ := rfl

/-- The monodromy maps as a canonical Mathlib complex representation. -/
noncomputable def zagierMonodromyRepresentation (b : zagierODERegularSet) :
    Representation ℂ (FundamentalGroup zagierODERegularSet b) (zagierSolutionGerms (b : ℂ)) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (zagierMonodromy b)

@[simp]
theorem zagierMonodromyRepresentation_apply (b : zagierODERegularSet)
    (g : FundamentalGroup zagierODERegularSet b) (φ : zagierSolutionGerms (b : ℂ)) :
    zagierMonodromyRepresentation b g φ = zagierMonodromy b g φ := rfl

theorem zagierMonodromyRepresentation_loop (b : zagierODERegularSet) (γ : Path b b)
    (φ : zagierSolutionGerms (b : ℂ)) :
    zagierMonodromyRepresentation b
      (FundamentalGroup.fromPath (X := TopCat.of zagierODERegularSet) ⟦γ⟧) φ =
        zagierPathTransport b γ φ := rfl

/-- The complex span of the monodromy translates of one actual solution germ. -/
noncomputable def zagierMonodromyOrbitSpan (b : zagierODERegularSet)
    (φ : zagierSolutionGerms (b : ℂ)) : Submodule ℂ (zagierSolutionGerms (b : ℂ)) :=
  Submodule.span ℂ (Set.range (fun g => zagierMonodromyRepresentation b g φ))

theorem self_mem_zagierMonodromyOrbitSpan (b : zagierODERegularSet)
    (φ : zagierSolutionGerms (b : ℂ)) : φ ∈ zagierMonodromyOrbitSpan b φ := by
  have h : zagierMonodromyRepresentation b 1 φ ∈ zagierMonodromyOrbitSpan b φ :=
    Submodule.subset_span ⟨1, rfl⟩
  simpa using h

theorem zagierMonodromyOrbitSpan_ne_bot (b : zagierODERegularSet)
    {φ : zagierSolutionGerms (b : ℂ)} (hφ : φ ≠ 0) : zagierMonodromyOrbitSpan b φ ≠ ⊥ := by
  intro h
  have hm := self_mem_zagierMonodromyOrbitSpan b φ
  rw [h, Submodule.mem_bot] at hm
  exact hφ hm

theorem zagierMonodromyOrbitSpan_mem_invtSubmodule (b : zagierODERegularSet)
    (φ : zagierSolutionGerms (b : ℂ)) :
    zagierMonodromyOrbitSpan b φ ∈ (zagierMonodromyRepresentation b).invtSubmodule := by
  rw [Representation.mem_invtSubmodule]
  intro g
  rw [Module.End.mem_invtSubmodule]
  apply Submodule.span_le.mpr
  rintro _ ⟨h, rfl⟩
  change zagierMonodromyRepresentation b g (zagierMonodromyRepresentation b h φ) ∈
    zagierMonodromyOrbitSpan b φ
  have he : zagierMonodromyRepresentation b g (zagierMonodromyRepresentation b h φ) =
      zagierMonodromyRepresentation b (g * h) φ := by
    rw [map_mul]
    rfl
  rw [he]
  exact Submodule.subset_span ⟨g * h, rfl⟩

theorem zagierMonodromyOrbitSpan_le (b : zagierODERegularSet)
    {φ : zagierSolutionGerms (b : ℂ)} {W : Submodule ℂ (zagierSolutionGerms (b : ℂ))}
    (hW : W ∈ (zagierMonodromyRepresentation b).invtSubmodule) (hφ : φ ∈ W) :
    zagierMonodromyOrbitSpan b φ ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact ((Representation.mem_invtSubmodule (zagierMonodromyRepresentation b)).mp hW g) hφ

end DirichletL
