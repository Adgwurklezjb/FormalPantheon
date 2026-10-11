import Mathlib

/-!
Explicit matrices for the finite-product argument on Gamma0(6), supporting
the modular identities in CDT v2 Section 11.1. The S/T certificates use
right cosets, in the order required by the right slash action.
-/

namespace DirichletL

open Matrix
open scoped MatrixGroups

/-- Twelve determinant-one integer matrices for the level-six norm. -/
def levelSixRep : Fin 12 → SL(2, ℤ) :=
  ![1, ModularGroup.S,
    ⟨!![0, -1; 1, 1], by norm_num [det_fin_two_of]⟩,
    ⟨!![0, -1; 1, 2], by norm_num [det_fin_two_of]⟩,
    ⟨!![0, -1; 1, 3], by norm_num [det_fin_two_of]⟩,
    ⟨!![0, -1; 1, 4], by norm_num [det_fin_two_of]⟩,
    ⟨!![0, -1; 1, 5], by norm_num [det_fin_two_of]⟩,
    ⟨!![1, 0; 2, 1], by norm_num [det_fin_two_of]⟩,
    ⟨!![1, 1; 2, 3], by norm_num [det_fin_two_of]⟩,
    ⟨!![1, 2; 2, 5], by norm_num [det_fin_two_of]⟩,
    ⟨!![1, 0; 3, 1], by norm_num [det_fin_two_of]⟩,
    ⟨!![2, 1; 3, 2], by norm_num [det_fin_two_of]⟩]

@[simp] theorem levelSixRep_zero : levelSixRep 0 = 1 := rfl

/-- The permutation of the level-six representatives under right multiplication by S. -/
def levelSixPermS : Equiv.Perm (Fin 12) where
  toFun := ![1, 0, 6, 9, 10, 7, 2, 5, 11, 3, 4, 8]
  invFun := ![1, 0, 6, 9, 10, 7, 2, 5, 11, 3, 4, 8]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The permutation of the level-six representatives under right multiplication by T. -/
def levelSixPermT : Equiv.Perm (Fin 12) where
  toFun := ![0, 2, 3, 4, 5, 6, 1, 8, 9, 7, 11, 10]
  invFun := ![0, 6, 1, 2, 3, 4, 5, 9, 7, 8, 11, 10]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem levelSixRep_mul_S_mem (i : Fin 12) :
    levelSixRep i * ModularGroup.S * (levelSixRep (levelSixPermS i))⁻¹ ∈
      CongruenceSubgroup.Gamma0 6 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  fin_cases i <;> decide

theorem levelSixRep_mul_T_mem (i : Fin 12) :
    levelSixRep i * ModularGroup.T * (levelSixRep (levelSixPermT i))⁻¹ ∈
      CongruenceSubgroup.Gamma0 6 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  fin_cases i <;> decide

end DirichletL
