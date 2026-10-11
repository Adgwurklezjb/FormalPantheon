import Analysis.WeightedCubicModularForm
import Arithmetic.CubicEisensteinWeights

/-!
The character laws and weight-six squares of the full cubic sums for
CDT v2, Section 11.1, and Zagier (2009), Section 6.
-/

namespace DirichletL

open CongruenceSubgroup
open _root_.UpperHalfPlane
open scoped MatrixGroups ModularForm

theorem betaCubicEisenstein_slash {A : SL(2, ℤ)} (hA : A ∈ Gamma0 6) :
    weightedCubicEisenstein betaCubicWeight ∣[(3 : ℤ)] A = fun τ =>
      (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) * weightedCubicEisenstein betaCubicWeight τ := by
  have hw : cubicEisensteinWeightSlash betaCubicWeight A = fun a =>
      (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) * betaCubicWeight a := by
    ext a
    exact (betaCubicWeight_vecMul a ((Gamma0 6).inv_mem hA)).trans
      (congrArg (fun n : ℤ => (n : ℂ) * betaCubicWeight a) (cubicResidueCharacter_Gamma0_inv hA))
  rw [weightedCubicEisenstein_slash, hw, weightedCubicEisenstein_const_mul]

theorem gammaCubicEisenstein_slash {A : SL(2, ℤ)} (hA : A ∈ Gamma0 6) :
    weightedCubicEisenstein gammaCubicWeight ∣[(3 : ℤ)] A = fun τ =>
      (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) * weightedCubicEisenstein gammaCubicWeight τ := by
  have hw : cubicEisensteinWeightSlash gammaCubicWeight A = fun a =>
      (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) * gammaCubicWeight a := by
    ext a
    exact (gammaCubicWeight_vecMul a ((Gamma0 6).inv_mem hA)).trans
      (congrArg (fun n : ℤ => (n : ℂ) * gammaCubicWeight a) (cubicResidueCharacter_Gamma0_inv hA))
  rw [weightedCubicEisenstein_slash, hw, weightedCubicEisenstein_const_mul]

/-- The square of a weighted cubic sum with the proved modulus-three character law. -/
noncomputable def weightedCubicSquareForm (w : (Fin 2 → ZMod 6) → ℂ)
    (hw : ∀ A : SL(2, ℤ), A ∈ Gamma0 6 →
      weightedCubicEisenstein w ∣[(3 : ℤ)] A = fun τ =>
        (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) * weightedCubicEisenstein w τ) :
    ModularForm (Gamma0 6) 6 where
  toFun τ := weightedCubicEisenstein w τ ^ 2
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    change (fun τ => weightedCubicEisenstein w τ ^ 2) ∣[(6 : ℤ)] A = _
    have he : (fun τ => weightedCubicEisenstein w τ ^ 2) =
        weightedCubicEisenstein w * weightedCubicEisenstein w := by
      ext τ
      simp only [pow_two, Pi.mul_apply]
    rw [he, show (6 : ℤ) = 3 + 3 by norm_num, ModularForm.mul_slash_SL2, hw A hA]
    ext τ
    simp only [Pi.mul_apply]
    have hc : (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) ^ 2 = 1 := by
      exact_mod_cast cubicResidueCharacter_Gamma0_sq hA
    calc
      _ = (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) ^ 2 *
          weightedCubicEisenstein w τ ^ 2 := by ring
      _ = _ := by rw [hc, one_mul, pow_two]
  holo' := by
    simpa only [pow_two] using
      (weightedCubicEisenstein_MDifferentiable w).mul (weightedCubicEisenstein_MDifferentiable w)
  bdd_at_cusps' := isBoundedAt_cusp_of_slash_SL2 (fun A => by
    have he : (fun τ => weightedCubicEisenstein w τ ^ 2) =
        weightedCubicEisenstein w * weightedCubicEisenstein w := by
      ext τ
      simp only [pow_two, Pi.mul_apply]
    change IsBoundedAtImInfty ((fun τ => weightedCubicEisenstein w τ ^ 2) ∣[(6 : ℤ)] A)
    rw [he, show (6 : ℤ) = 3 + 3 by norm_num, ModularForm.mul_slash_SL2]
    exact (isBoundedAtImInfty_weightedCubicEisenstein_slash w A).mul
      (isBoundedAtImInfty_weightedCubicEisenstein_slash w A))

@[simp] theorem weightedCubicSquareForm_apply (w : (Fin 2 → ZMod 6) → ℂ)
    (hw : ∀ A : SL(2, ℤ), A ∈ Gamma0 6 →
      weightedCubicEisenstein w ∣[(3 : ℤ)] A = fun τ =>
        (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) * weightedCubicEisenstein w τ) (τ : ℍ) :
    weightedCubicSquareForm w hw τ = weightedCubicEisenstein w τ ^ 2 := rfl

/-- The square of the full beta lattice sum as a weight-six form on Γ₀(6). -/
noncomputable def betaCubicSquareForm : ModularForm (Gamma0 6) 6 :=
  weightedCubicSquareForm betaCubicWeight (fun _ hA => betaCubicEisenstein_slash hA)

/-- The square of the full gamma lattice sum as a weight-six form on Γ₀(6). -/
noncomputable def gammaCubicSquareForm : ModularForm (Gamma0 6) 6 :=
  weightedCubicSquareForm gammaCubicWeight (fun _ hA => gammaCubicEisenstein_slash hA)

@[simp] theorem betaCubicSquareForm_apply (τ : ℍ) :
    betaCubicSquareForm τ = weightedCubicEisenstein betaCubicWeight τ ^ 2 := rfl

@[simp] theorem gammaCubicSquareForm_apply (τ : ℍ) :
    gammaCubicSquareForm τ = weightedCubicEisenstein gammaCubicWeight τ ^ 2 := rfl

end DirichletL
