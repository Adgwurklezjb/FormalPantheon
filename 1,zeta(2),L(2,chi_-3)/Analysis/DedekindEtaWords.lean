import Arithmetic.ModularWords
import Analysis.DedekindEtaTransformations
import Analysis.ModularSlash

/-!
Exact eta-square multipliers for finite S/T words. The S and T input
identities have the normalization of DLMF 23.18.5 and 27.14.12.
These word formulas support CDT v2 Section 11.1, equation `haupt`.
-/

namespace DirichletL

open Complex
open _root_.UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm

/-- The translation multiplier of eta squared. -/
noncomputable def dedekindEtaRoot : ℂ := exp (π * I / 6)

theorem dedekindEtaRoot_ne_zero : dedekindEtaRoot ≠ 0 := exp_ne_zero _

theorem dedekindEtaRoot_pow_twelve : dedekindEtaRoot ^ 12 = 1 := by
  rw [dedekindEtaRoot, ← exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have he : (12 : ℂ) * (π * I / 6) = 2 * π * I := by ring
  rw [he, exp_two_pi_mul_I]

theorem dedekindEtaRoot_zpow_neg_three : dedekindEtaRoot ^ (-3 : ℤ) = -I := by
  rw [zpow_neg, zpow_ofNat, dedekindEtaRoot, ← exp_nat_mul]
  simp only [Nat.cast_ofNat]
  have he : (3 : ℂ) * (π * I / 6) = π / 2 * I := by ring
  rw [he, exp_pi_div_two_mul_I]
  simp

theorem dedekindEtaRoot_zpow_eq_one_of_dvd {n : ℤ} (hn : 12 ∣ n) :
    dedekindEtaRoot ^ n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  rw [zpow_mul, show dedekindEtaRoot ^ (12 : ℤ) = 1 from dedekindEtaRoot_pow_twelve,
    one_zpow]

theorem dedekindEta_sq_slash_S :
    (fun τ : ℍ => dedekindEta τ ^ 2) ∣[(1 : ℤ)] ModularGroup.S =
      dedekindEtaRoot ^ (-3 : ℤ) • (fun τ : ℍ => dedekindEta τ ^ 2) := by
  apply (slash_eq_smul_iff _ _ _ _).mpr
  intro τ
  have h10 : ((ModularGroup.S 1 0 : ℤ) : ℂ) = 1 := by norm_num [ModularGroup.S]
  have h11 : ((ModularGroup.S 1 1 : ℤ) : ℂ) = 0 := by norm_num [ModularGroup.S]
  have hs : ((-I * (τ : ℂ)) ^ (1 / 2 : ℂ)) ^ 2 = -I * τ := by
    simpa only [one_div] using cpow_nat_inv_pow (-I * (τ : ℂ)) (n := 2) two_ne_zero
  have he := congrArg (fun z : ℂ => z ^ 2) (dedekindEta_neg_inv τ.im_pos)
  dsimp only at he
  rw [mul_pow, hs] at he
  simpa only [dedekindEtaRoot_zpow_neg_three, h10, h11, one_mul, add_zero,
    zpow_one, modular_S_smul, coe_mk, inv_neg, neg_div, one_div] using he

theorem dedekindEta_sq_slash_T :
    (fun τ : ℍ => dedekindEta τ ^ 2) ∣[(1 : ℤ)] ModularGroup.T =
      dedekindEtaRoot • (fun τ : ℍ => dedekindEta τ ^ 2) := by
  apply (slash_eq_smul_iff _ _ _ _).mpr
  intro τ
  have h10 : ((ModularGroup.T 1 0 : ℤ) : ℂ) = 0 := by norm_num [ModularGroup.T]
  have h11 : ((ModularGroup.T 1 1 : ℤ) : ℂ) = 1 := by norm_num [ModularGroup.T]
  have hT : ((ModularGroup.T • τ : ℍ) : ℂ) = τ + 1 := by
    simpa using ModularGroup.coe_T_zpow_smul_eq τ (n := 1)
  have he := congrArg (fun z : ℂ => z ^ 2) (dedekindEta_add_one (τ : ℂ))
  dsimp only at he
  rw [mul_pow, ← exp_nat_mul] at he
  simp only [Nat.cast_ofNat] at he
  have hexp : (2 : ℂ) * (π * I / 12) = π * I / 6 := by ring
  rw [hexp] at he
  simpa only [dedekindEtaRoot, h10, h11, zero_mul, zero_add, one_zpow, mul_one, hT]
    using he

theorem dedekindEta_sq_slash_T_zpow (n : ℤ) :
    (fun τ : ℍ => dedekindEta τ ^ 2) ∣[(1 : ℤ)] (ModularGroup.T ^ n) =
      dedekindEtaRoot ^ n • (fun τ : ℍ => dedekindEta τ ^ 2) :=
  slash_zpow_of_eq_smul _ _ _ dedekindEtaRoot_ne_zero dedekindEta_sq_slash_T n

theorem dedekindEta_sq_slash_word (w : List ℤ) :
    (fun τ : ℍ => dedekindEta τ ^ 2) ∣[(1 : ℤ)] modularWordMatrix w =
      dedekindEtaRoot ^ modularWordExponent w • (fun τ : ℍ => dedekindEta τ ^ 2) := by
  induction w with
  | nil => simp [modularWordMatrix, modularWordExponent]
  | cons n w ih =>
    change (fun τ : ℍ => dedekindEta τ ^ 2) ∣[(1 : ℤ)]
      ((ModularGroup.T ^ n * ModularGroup.S) * modularWordMatrix w) =
        dedekindEtaRoot ^ (n - 3 + modularWordExponent w) • _
    rw [SlashAction.slash_mul, SlashAction.slash_mul, dedekindEta_sq_slash_T_zpow,
      ModularForm.SL_smul_slash, dedekindEta_sq_slash_S, smul_smul,
      ModularForm.SL_smul_slash, ih, smul_smul,
      ← zpow_add₀ dedekindEtaRoot_ne_zero, ← zpow_add₀ dedekindEtaRoot_ne_zero]
    simp only [sub_eq_add_neg]

theorem dedekindEta_sq_word_apply (w : List ℤ) (τ : ℍ) :
    dedekindEta ((modularWordMatrix w • τ : ℍ) : ℂ) ^ 2 =
      dedekindEtaRoot ^ modularWordExponent w *
        (((modularWordMatrix w) 1 0 : ℂ) * τ + ((modularWordMatrix w) 1 1 : ℂ)) *
          dedekindEta τ ^ 2 := by
  simpa only [zpow_one] using
    (slash_eq_smul_iff _ _ _ _).mp (dedekindEta_sq_slash_word w) τ

end DirichletL
