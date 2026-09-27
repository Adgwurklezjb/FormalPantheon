import Analysis.NumeratorSquareModularForms
import Analysis.ZagierEtaModular

/-!
The weight-six product sides for the beta/gamma numerator comparison.
Source: CDT v2, Section 11.1; Zagier (2009), Sections 5-6.
-/

namespace DirichletL

open CongruenceSubgroup
open _root_.UpperHalfPlane

/-- A triple product of the three actual case-C weight-two eta forms. -/
noncomputable def zagierEtaTripleForm (r s t : Fin 3) : ModularForm (Gamma0 6) 6 :=
  ((zagierEtaWeightTwoForm r).mul (zagierEtaWeightTwoForm s)).mul (zagierEtaWeightTwoForm t)

theorem zagierEtaTripleForm_apply (r s t : Fin 3) (τ : ℍ) :
    zagierEtaTripleForm r s t τ =
      hauptmodulEta τ ^ (r.val + s.val + t.val) * zagierEtaSquare τ ^ 3 := by
  change (zagierEtaWeightTwoForm r τ * zagierEtaWeightTwoForm s τ) *
    zagierEtaWeightTwoForm t τ = _
  rw [zagierEtaWeightTwoForm_eq, zagierEtaWeightTwoForm_eq, zagierEtaWeightTwoForm_eq]
  simp only [pow_add]
  ring

/-- The proposed square of the beta numerator, with all modularity conditions proved. -/
noncomputable def betaNumeratorProductSquareForm : ModularForm (Gamma0 6) 6 :=
  zagierEtaTripleForm 0 1 1 - 20 • zagierEtaTripleForm 1 1 1 +
    118 • zagierEtaTripleForm 1 1 2 - 180 • zagierEtaTripleForm 1 2 2 +
    81 • zagierEtaTripleForm 2 2 2

/-- The proposed square of the gamma numerator as an actual weight-six form. -/
noncomputable def gammaNumeratorProductSquareForm : ModularForm (Gamma0 6) 6 :=
  zagierEtaTripleForm 0 1 1 - 18 • zagierEtaTripleForm 1 1 1 +
    81 • zagierEtaTripleForm 1 1 2

theorem betaNumeratorProductSquareForm_apply (τ : ℍ) :
    betaNumeratorProductSquareForm τ =
      hauptmodulEta τ ^ 2 * (1 - 10 * hauptmodulEta τ + 9 * hauptmodulEta τ ^ 2) ^ 2 *
        zagierEtaSquare τ ^ 3 := by
  simp only [betaNumeratorProductSquareForm, ModularForm.add_apply, ModularForm.sub_apply,
    ModularForm.smul_apply, zagierEtaTripleForm_apply, nsmul_eq_mul]
  norm_num
  ring

theorem gammaNumeratorProductSquareForm_apply (τ : ℍ) :
    gammaNumeratorProductSquareForm τ =
      hauptmodulEta τ ^ 2 * (1 - 9 * hauptmodulEta τ) ^ 2 * zagierEtaSquare τ ^ 3 := by
  simp only [gammaNumeratorProductSquareForm, ModularForm.add_apply, ModularForm.sub_apply,
    ModularForm.smul_apply, zagierEtaTripleForm_apply, nsmul_eq_mul]
  norm_num
  ring

/-- The difference whose vanishing proves the beta numerator-square identity. -/
noncomputable def betaNumeratorSquareDifferenceForm : ModularForm (Gamma0 6) 6 :=
  betaNumeratorSquareForm - betaNumeratorProductSquareForm

/-- The corresponding gamma numerator-square difference. -/
noncomputable def gammaNumeratorSquareDifferenceForm : ModularForm (Gamma0 6) 6 :=
  gammaNumeratorSquareForm - gammaNumeratorProductSquareForm

theorem betaNumeratorSquareDifferenceForm_apply (τ : ℍ) :
    betaNumeratorSquareDifferenceForm τ =
      (∑' n : ℕ, (betaNumerator n : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ n) ^ 2 -
        hauptmodulEta τ ^ 2 * (1 - 10 * hauptmodulEta τ + 9 * hauptmodulEta τ ^ 2) ^ 2 *
          zagierEtaSquare τ ^ 3 := by
  rw [betaNumeratorSquareDifferenceForm, ModularForm.sub_apply,
    betaNumeratorSquareForm_apply, betaNumeratorProductSquareForm_apply]

theorem gammaNumeratorSquareDifferenceForm_apply (τ : ℍ) :
    gammaNumeratorSquareDifferenceForm τ =
      (∑' n : ℕ, (gammaNumerator n : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ n) ^ 2 -
        hauptmodulEta τ ^ 2 * (1 - 9 * hauptmodulEta τ) ^ 2 * zagierEtaSquare τ ^ 3 := by
  rw [gammaNumeratorSquareDifferenceForm, ModularForm.sub_apply,
    gammaNumeratorSquareForm_apply, gammaNumeratorProductSquareForm_apply]

end DirichletL
