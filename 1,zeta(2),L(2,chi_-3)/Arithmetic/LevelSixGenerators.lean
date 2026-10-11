import Arithmetic.LevelSixMatrices

/-!
The twelve right-coset representatives give explicit generators of Gamma0(6).
This applies Mathlib's Schreier lemma to the finite S/T certificates, supporting
the modular identities in CDT v2 Section 11.1.
-/

namespace DirichletL

open scoped MatrixGroups Pointwise

theorem levelSixRep_mul_inv_mem_iff (i j : Fin 12) :
    levelSixRep i * (levelSixRep j)⁻¹ ∈ CongruenceSubgroup.Gamma0 6 ↔ i = j := by
  rw [CongruenceSubgroup.Gamma0_mem]
  fin_cases i <;> fin_cases j <;> decide

private theorem levelSixRep_mul_generator_mem (A : SL(2, ℤ))
    (hA : A ∈ ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ))) :
    ∃ p : Equiv.Perm (Fin 12), ∀ i,
      levelSixRep i * A * (levelSixRep (p i))⁻¹ ∈ CongruenceSubgroup.Gamma0 6 := by
  rcases Set.mem_insert_iff.mp hA with rfl | hA
  · exact ⟨levelSixPermS, levelSixRep_mul_S_mem⟩
  · obtain rfl := Set.mem_singleton_iff.mp hA
    exact ⟨levelSixPermT, levelSixRep_mul_T_mem⟩

theorem exists_levelSixRep_mul_inv_mem (γ : SL(2, ℤ)) :
    ∃ i : Fin 12, γ * (levelSixRep i)⁻¹ ∈ CongruenceSubgroup.Gamma0 6 := by
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  induction hγ using Subgroup.closure_induction_right with
  | one => exact ⟨0, by simp⟩
  | mul_right γ _ A hA ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨p, hp⟩ := levelSixRep_mul_generator_mem A hA
    refine ⟨p i, ?_⟩
    rw [show γ * A * (levelSixRep (p i))⁻¹ =
      (γ * (levelSixRep i)⁻¹) *
        (levelSixRep i * A * (levelSixRep (p i))⁻¹) by group]
    exact (CongruenceSubgroup.Gamma0 6).mul_mem hi (hp i)
  | mul_inv_cancel γ _ A hA ih =>
    obtain ⟨i, hi⟩ := ih
    obtain ⟨p, hp⟩ := levelSixRep_mul_generator_mem A hA
    have hj : levelSixRep (p.symm i) * A * (levelSixRep i)⁻¹ ∈
        CongruenceSubgroup.Gamma0 6 := by simpa using hp (p.symm i)
    refine ⟨p.symm i, ?_⟩
    rw [show γ * A⁻¹ * (levelSixRep (p.symm i))⁻¹ =
      (γ * (levelSixRep i)⁻¹) *
        (levelSixRep (p.symm i) * A * (levelSixRep i)⁻¹)⁻¹ by group]
    exact (CongruenceSubgroup.Gamma0 6).mul_mem hi
      ((CongruenceSubgroup.Gamma0 6).inv_mem hj)

theorem levelSixRep_isComplement :
    Subgroup.IsComplement (CongruenceSubgroup.Gamma0 6 : Set SL(2, ℤ))
      (Set.range levelSixRep) := by
  apply Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mpr
  intro γ
  obtain ⟨i, hi⟩ := exists_levelSixRep_mul_inv_mem γ
  refine ⟨⟨levelSixRep i, Set.mem_range_self i⟩, hi, ?_⟩
  rintro ⟨r, hr⟩ hj
  obtain ⟨j, rfl⟩ := hr
  apply Subtype.ext
  apply congrArg levelSixRep
  apply (levelSixRep_mul_inv_mem_iff j i).mp
  rw [show levelSixRep j * (levelSixRep i)⁻¹ =
    (γ * (levelSixRep j)⁻¹)⁻¹ * (γ * (levelSixRep i)⁻¹) by group]
  exact (CongruenceSubgroup.Gamma0 6).mul_mem
    ((CongruenceSubgroup.Gamma0 6).inv_mem hj) hi

/-- The two lists of Schreier generators attached to the level-six representatives. -/
def levelSixGenerators : Set SL(2, ℤ) :=
  Set.range (fun i => levelSixRep i * ModularGroup.S *
    (levelSixRep (levelSixPermS i))⁻¹) ∪
  Set.range (fun i => levelSixRep i * ModularGroup.T *
    (levelSixRep (levelSixPermT i))⁻¹)

theorem levelSixGenerators_subset :
    levelSixGenerators ⊆ CongruenceSubgroup.Gamma0 6 := by
  rintro γ (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact levelSixRep_mul_S_mem i
  · exact levelSixRep_mul_T_mem i

private theorem levelSix_toRightFun_eq (γ : SL(2, ℤ)) (i : Fin 12)
    (hi : γ * (levelSixRep i)⁻¹ ∈ CongruenceSubgroup.Gamma0 6) :
    (levelSixRep_isComplement.toRightFun γ : SL(2, ℤ)) = levelSixRep i := by
  have he : levelSixRep_isComplement.toRightFun γ =
      ⟨levelSixRep i, Set.mem_range_self i⟩ :=
    (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp levelSixRep_isComplement γ).unique
      (levelSixRep_isComplement.mul_inv_toRightFun_mem γ) hi
  exact congrArg Subtype.val he

theorem closure_levelSixGenerators :
    Subgroup.closure levelSixGenerators = CongruenceSubgroup.Gamma0 6 := by
  have hR1 : (1 : SL(2, ℤ)) ∈ Set.range levelSixRep := ⟨0, rfl⟩
  have h := Subgroup.closure_mul_image_eq levelSixRep_isComplement hR1
    SpecialLinearGroup.SL2Z_generators
  have hset : ((Set.range levelSixRep * {ModularGroup.S, ModularGroup.T}).image
      fun γ => γ * (levelSixRep_isComplement.toRightFun γ : SL(2, ℤ))⁻¹) =
      levelSixGenerators := by
    ext γ
    constructor
    · rintro ⟨m, ⟨r, hr, A, hA, rfl⟩, rfl⟩
      obtain ⟨i, rfl⟩ := hr
      rcases Set.mem_insert_iff.mp hA with rfl | hA
      · dsimp only
        rw [levelSix_toRightFun_eq _ _ (levelSixRep_mul_S_mem i)]
        exact Or.inl (Set.mem_range_self i)
      · obtain rfl := Set.mem_singleton_iff.mp hA
        dsimp only
        rw [levelSix_toRightFun_eq _ _ (levelSixRep_mul_T_mem i)]
        exact Or.inr (Set.mem_range_self i)
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · refine ⟨levelSixRep i * ModularGroup.S,
          Set.mul_mem_mul (Set.mem_range_self i) (by simp), ?_⟩
        dsimp only
        rw [levelSix_toRightFun_eq _ _ (levelSixRep_mul_S_mem i)]
      · refine ⟨levelSixRep i * ModularGroup.T,
          Set.mul_mem_mul (Set.mem_range_self i) (by simp), ?_⟩
        dsimp only
        rw [levelSix_toRightFun_eq _ _ (levelSixRep_mul_T_mem i)]
  simpa only [hset] using h

end DirichletL
