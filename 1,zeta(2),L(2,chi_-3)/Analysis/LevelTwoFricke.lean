import Analysis.LevelTwoModular

/-!
The exact inversion product for CDT author Lemma A.4.4, page 205.
Meanings, normalization, and nonzero factors precede the body in
-/

namespace DirichletL

open Complex Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped MatrixGroups

theorem levelTwoHauptmodul_S_mul_half (τ : ℍ) :
    levelTwoHauptmodul (Function.Periodic.qParam 1 (ModularGroup.S • τ : ℍ)) *
      levelTwoHauptmodul (Function.Periodic.qParam 1 ((τ : ℂ) / 2)) = 16 := by
  have hh : 0 < ((τ : ℂ) / 2).im := by simpa using half_pos τ.im_pos
  let σ : ℍ := ⟨(τ : ℂ) / 2, hh⟩
  have hτ0 : (τ : ℂ) ≠ 0 := fun h => (ne_of_gt τ.im_pos) (congrArg Complex.im h)
  have he0 : dedekindEta τ ≠ 0 := dedekindEta_ne_zero τ.im_pos
  have heh0 : dedekindEta ((τ : ℂ) / 2) ≠ 0 := dedekindEta_ne_zero hh
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
    rw [coe_specialLinearGroup_apply]
    norm_num [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast, ModularGroup.S]
  change levelTwoHauptmodul (qParam 1 (ModularGroup.S • τ : ℍ)) *
    levelTwoHauptmodul (qParam 1 σ) = 16
  rw [levelTwoHauptmodul_qParam_eq_eta, levelTwoHauptmodul_qParam_eq_eta, hS]
  change (-256 * dedekindEta (2 * (-1 / (τ : ℂ))) ^ 24 /
      dedekindEta (-1 / (τ : ℂ)) ^ 24) *
    (-256 * dedekindEta (2 * ((τ : ℂ) / 2)) ^ 24 /
      dedekindEta ((τ : ℂ) / 2) ^ 24) = 16
  rw [show (2 : ℂ) * (-1 / (τ : ℂ)) = -1 / ((τ : ℂ) / 2) by field_simp,
    show (2 : ℂ) * ((τ : ℂ) / 2) = (τ : ℂ) by ring,
    dedekindEta_neg_inv_pow_twenty_four hh,
    dedekindEta_neg_inv_pow_twenty_four τ.im_pos]
  field_simp [hτ0, he0, heh0]
  ring

end DirichletL
