import Mathlib

/-!
Full cubic Eisenstein sums with coefficients depending on residues modulo six.
These support the two weight-three series in CDT v2, Section 11.1,
-/

namespace DirichletL

open Complex hiding Gamma
open Matrix ModularForm CongruenceSubgroup EisensteinSeries
open _root_.UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- The full cubic lattice sum with a complex weight on residue pairs modulo six. -/
noncomputable def weightedCubicEisenstein (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) : ℂ :=
  ∑' v : Fin 2 → ℤ, w (fun i => (v i : ZMod 6)) * eisSummand 3 v τ

/-- Transport of a residue weight by the inverse row action of an integral matrix. -/
noncomputable def cubicEisensteinWeightSlash (w : (Fin 2 → ZMod 6) → ℂ) (A : SL(2, ℤ)) :
    (Fin 2 → ZMod 6) → ℂ :=
  fun a => w (a ᵥ* ((A⁻¹ : SL(2, ℤ)) : SL(2, ZMod 6)))

/-- The canonical equivalence on lattice rows induced by a determinant-one matrix. -/
private noncomputable def cubicLatticeEquiv (A : SL(2, ℤ)) :
    (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
  (Matrix.toLinearEquivRight'OfInv
    (show (↑(A⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) * ↑A = 1 by
      rw [← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one])
    (show (↑A : Matrix (Fin 2) (Fin 2) ℤ) * ↑(A⁻¹) = 1 by
      rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one])).toEquiv

private theorem intCast_vecMul_sl (v : Fin 2 → ℤ) (A : SL(2, ℤ)) :
    (fun i : Fin 2 => ((v ᵥ* A) i : ZMod 6)) =
      (fun i => (v i : ZMod 6)) ᵥ* (A : SL(2, ZMod 6)) := by
  exact funext ((Int.castRingHom (ZMod 6)).map_vecMul (m := Fin 2) (n := Fin 2) A v)

theorem weightedCubicEisenstein_slash (w : (Fin 2 → ZMod 6) → ℂ) (A : SL(2, ℤ)) :
    weightedCubicEisenstein w ∣[(3 : ℤ)] A =
      weightedCubicEisenstein (cubicEisensteinWeightSlash w A) := by
  ext z
  have hr : (∑' v : Fin 2 → ℤ,
      w (fun i => (v i : ZMod 6)) * eisSummand 3 (v ᵥ* A) z) =
      weightedCubicEisenstein (cubicEisensteinWeightSlash w A) z := by
    rw [weightedCubicEisenstein, ← (cubicLatticeEquiv A).tsum_eq
      (fun v => cubicEisensteinWeightSlash w A (fun i => (v i : ZMod 6)) *
        eisSummand 3 v z)]
    apply tsum_congr
    intro v
    have he : cubicLatticeEquiv A v = v ᵥ* A := by
      ext i
      simp only [cubicLatticeEquiv, LinearEquiv.coe_toEquiv,
        Matrix.toLinearEquivRight'OfInv_apply, Matrix.toLinearMapRight'_apply]
    simp only [he, cubicEisensteinWeightSlash]
    rw [intCast_vecMul_sl, vecMul_vecMul, ← SpecialLinearGroup.coe_mul]
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Int.coe_castRingHom, map_inv, mul_inv_cancel, SpecialLinearGroup.coe_one, vecMul_one]
  simp only [SL_slash_apply, _root_.zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| z.denom_ne_zero _)]
  change weightedCubicEisenstein w (A • z) =
    weightedCubicEisenstein (cubicEisensteinWeightSlash w A) z * denom A z ^ (3 : ℤ)
  rw [← hr, weightedCubicEisenstein, ← tsum_mul_right]
  apply tsum_congr
  intro v
  rw [eisSummand_SL2_apply]
  ring

theorem cubicEisensteinWeightSlash_eq_self (w : (Fin 2 → ZMod 6) → ℂ)
    {A : SL(2, ℤ)} (hA : A ∈ Gamma 6) : cubicEisensteinWeightSlash w A = w := by
  ext a
  simp only [cubicEisensteinWeightSlash, Gamma_mem'.mp ((Gamma 6).inv_mem hA),
    SpecialLinearGroup.coe_one, vecMul_one]

theorem weightedCubicEisenstein_const_mul (c : ℂ) (w : (Fin 2 → ZMod 6) → ℂ) :
    weightedCubicEisenstein (fun a => c * w a) = fun τ => c * weightedCubicEisenstein w τ := by
  ext τ
  simp only [weightedCubicEisenstein, mul_assoc, tsum_mul_left]

/-- The full weighted cubic sum as a form invariant under the principal level-six group. -/
noncomputable def weightedCubicEisensteinSIF (w : (Fin 2 → ZMod 6) → ℂ) :
    SlashInvariantForm (Gamma 6) 3 where
  toFun := weightedCubicEisenstein w
  slash_action_eq' A hA := by
    obtain ⟨A, hA, rfl⟩ := hA
    change weightedCubicEisenstein w ∣[(3 : ℤ)] A = weightedCubicEisenstein w
    rw [weightedCubicEisenstein_slash, cubicEisensteinWeightSlash_eq_self w hA]

@[simp] theorem weightedCubicEisensteinSIF_apply (w : (Fin 2 → ZMod 6) → ℂ) (τ : ℍ) :
    weightedCubicEisensteinSIF w τ = weightedCubicEisenstein w τ := rfl

end DirichletL
