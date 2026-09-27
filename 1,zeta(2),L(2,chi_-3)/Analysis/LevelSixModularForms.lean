import Arithmetic.LevelSixGenerators
import Analysis.ModularSlash

/-!
Finite transformation and cusp checks for modular forms on Gamma0(6), using
the canonical Mathlib structures. This supplies a construction interface for
the trivial-character modular identities in CDT v2 Section 11.1.
-/

namespace DirichletL

open Complex UpperHalfPlane
open scoped Topology Manifold MatrixGroups ModularForm

theorem slashInvariant_levelSix_of_rep_mul_S_of_rep_mul_T (k : ℤ) (f : ℍ → ℂ)
    (hS : ∀ i, f ∣[k] (levelSixRep i * ModularGroup.S *
      (levelSixRep (levelSixPermS i))⁻¹) = f)
    (hT : ∀ i, f ∣[k] (levelSixRep i * ModularGroup.T *
      (levelSixRep (levelSixPermT i))⁻¹) = f)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 6) : f ∣[k] γ = f := by
  rw [← closure_levelSixGenerators] at hγ
  induction hγ using Subgroup.closure_induction with
  | mem γ hγ =>
    rcases hγ with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact hS i
    · exact hT i
  | one => simp
  | mul γ δ _ _ hγ hδ => rw [SlashAction.slash_mul, hγ, hδ]
  | inv γ _ hγ =>
    have h := SlashAction.slash_mul k γ γ⁻¹ f
    simpa only [mul_inv_cancel, SlashAction.slash_one, hγ] using h.symm

/-- Bundle the twenty-four level-six transformation checks as slash invariance. -/
def levelSixSlashInvariantForm (k : ℤ) (f : ℍ → ℂ)
    (hS : ∀ i, f ∣[k] (levelSixRep i * ModularGroup.S *
      (levelSixRep (levelSixPermS i))⁻¹) = f)
    (hT : ∀ i, f ∣[k] (levelSixRep i * ModularGroup.T *
      (levelSixRep (levelSixPermT i))⁻¹) = f) :
    SlashInvariantForm (CongruenceSubgroup.Gamma0 6) k where
  toFun := f
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    exact slashInvariant_levelSix_of_rep_mul_S_of_rep_mul_T k f hS hT A hA

@[simp] theorem levelSixSlashInvariantForm_coe (k : ℤ) (f : ℍ → ℂ) (hS hT) :
    ⇑(levelSixSlashInvariantForm k f hS hT) = f := rfl

theorem exists_slash_eq_levelSixRep {k : ℤ}
    (f : SlashInvariantForm (CongruenceSubgroup.Gamma0 6) k) (γ : SL(2, ℤ)) :
    ∃ i : Fin 12, ⇑f ∣[k] γ = ⇑f ∣[k] levelSixRep i := by
  obtain ⟨i, hi⟩ := exists_levelSixRep_mul_inv_mem γ
  refine ⟨i, ?_⟩
  calc
    ⇑f ∣[k] γ = ⇑f ∣[k] ((γ * (levelSixRep i)⁻¹) * levelSixRep i) := by
      rw [inv_mul_cancel_right]
    _ = ⇑f ∣[k] levelSixRep i := by
      have hinv := SlashInvariantForm.slash_action_eqn f
        ((γ * (levelSixRep i)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ)
        ⟨γ * (levelSixRep i)⁻¹, hi, rfl⟩
      change ⇑f ∣[k] (γ * (levelSixRep i)⁻¹) = ⇑f at hinv
      rw [SlashAction.slash_mul, hinv]

theorem isBoundedAtImInfty_slash_levelSix_of_reps {k : ℤ}
    (f : SlashInvariantForm (CongruenceSubgroup.Gamma0 6) k)
    (hf : ∀ i : Fin 12, IsBoundedAtImInfty (⇑f ∣[k] levelSixRep i)) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (⇑f ∣[k] γ) := by
  obtain ⟨i, hi⟩ := exists_slash_eq_levelSixRep f γ
  rw [hi]
  exact hf i

/-- A level-six modular form from finite transformation laws and cusp bounds. -/
def levelSixModularForm (k : ℤ) (f : ℍ → ℂ)
    (hS : ∀ i, f ∣[k] (levelSixRep i * ModularGroup.S *
      (levelSixRep (levelSixPermS i))⁻¹) = f)
    (hT : ∀ i, f ∣[k] (levelSixRep i * ModularGroup.T *
      (levelSixRep (levelSixPermT i))⁻¹) = f)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbdd : ∀ i : Fin 12, IsBoundedAtImInfty (f ∣[k] levelSixRep i)) :
    ModularForm (CongruenceSubgroup.Gamma0 6) k where
  toSlashInvariantForm := levelSixSlashInvariantForm k f hS hT
  holo' := hhol
  bdd_at_cusps' := isBoundedAt_cusp_of_slash_SL2
    (isBoundedAtImInfty_slash_levelSix_of_reps (levelSixSlashInvariantForm k f hS hT) hbdd)

@[simp] theorem levelSixModularForm_coe (k : ℤ) (f : ℍ → ℂ) (hS hT hhol hbdd) :
    ⇑(levelSixModularForm k f hS hT hhol hbdd) = f := rfl

end DirichletL
