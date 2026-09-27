import Mathlib

/-!
The three left cosets needed in the specialized fiber step of CDT author
Lemma A.4.4, page 205. Meanings and matrix directions precede the body in
-/

namespace DirichletL

open scoped MatrixGroups

theorem exists_levelTwo_left_coset (γ : SL(2, ℤ)) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma0 2 ∧
      (γ = δ ∨ γ = δ * ModularGroup.S ∨
        γ = δ * (ModularGroup.S * ModularGroup.T)) := by
  by_cases hc : (γ 1 0 : ZMod 2) = 0
  · exact ⟨γ, CongruenceSubgroup.Gamma0_mem.mpr hc, Or.inl rfl⟩
  by_cases hd : (γ 1 1 : ZMod 2) = 0
  · have hrow : (γ * ModularGroup.S⁻¹) 1 0 = -γ 1 1 := by
      change (γ.1 * Matrix.adjugate ModularGroup.S.1) 1 0 = _
      simp [ModularGroup.S, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    refine ⟨γ * ModularGroup.S⁻¹, ?_, Or.inr (Or.inl ?_)⟩
    · apply CongruenceSubgroup.Gamma0_mem.mpr
      rw [hrow]
      simpa only [Int.cast_neg, neg_eq_zero] using hd
    · simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hone (x : ZMod 2) (hx : x ≠ 0) : x = 1 := by
    fin_cases x <;> norm_num at *
  have hc1 := hone (γ 1 0 : ZMod 2) hc
  have hd1 := hone (γ 1 1 : ZMod 2) hd
  have hrow : (γ * (ModularGroup.S * ModularGroup.T)⁻¹) 1 0 = γ 1 0 - γ 1 1 := by
    change (γ.1 * Matrix.adjugate (ModularGroup.S.1 * ModularGroup.T.1)) 1 0 = _
    simp [ModularGroup.S, ModularGroup.T, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, sub_eq_add_neg]
  refine ⟨γ * (ModularGroup.S * ModularGroup.T)⁻¹, ?_, Or.inr (Or.inr ?_)⟩
  · apply CongruenceSubgroup.Gamma0_mem.mpr
    rw [hrow, Int.cast_sub, hc1, hd1, sub_self]
  · simp only [mul_assoc, inv_mul_cancel, mul_one]

end DirichletL
