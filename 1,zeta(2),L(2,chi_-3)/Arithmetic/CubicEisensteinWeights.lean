import Foundations.ChiMinusThree

/-!
The residue weights for the two cubic Eisenstein series of CDT v2, Section 11.1,
-/

namespace DirichletL

open Matrix CongruenceSubgroup
open scoped MatrixGroups

/-- The canonical character modulo three, pulled back to residue classes modulo six. -/
noncomputable def cubicResidueCharacter (a : ZMod 6) : ℤ :=
  quadraticChar (ZMod 3) (ZMod.castHom (by norm_num : 3 ∣ 6) (ZMod 3) a)

theorem cubicResidueCharacter_intCast (n : ℤ) :
    cubicResidueCharacter (n : ZMod 6) = legendreSym 3 n := by
  simp only [cubicResidueCharacter, map_intCast, legendreSym]

@[simp] theorem cubicResidueCharacter_zero : cubicResidueCharacter 0 = 0 := by
  simp only [cubicResidueCharacter, map_zero, quadraticChar_zero]

@[simp] theorem cubicResidueCharacter_one : cubicResidueCharacter 1 = 1 := by
  simp only [cubicResidueCharacter, map_one]

theorem cubicResidueCharacter_neg_one : cubicResidueCharacter (-1) = -1 := by
  have h := cubicResidueCharacter_intCast (-1)
  norm_num at h
  exact h

theorem cubicResidueCharacter_mul (a b : ZMod 6) :
    cubicResidueCharacter (a * b) = cubicResidueCharacter a * cubicResidueCharacter b := by
  simp only [cubicResidueCharacter, map_mul]

@[simp] theorem cubicResidueCharacter_neg (a : ZMod 6) :
    cubicResidueCharacter (-a) = -cubicResidueCharacter a := by
  rw [← neg_one_mul a, cubicResidueCharacter_mul, cubicResidueCharacter_neg_one, neg_one_mul]

theorem cubicResidueCharacter_three_mul_add (b y : ZMod 6) :
    cubicResidueCharacter (3 * b + y) = cubicResidueCharacter y := by
  simp only [cubicResidueCharacter, map_add, map_mul, map_ofNat,
    show (3 : ZMod 3) = 0 by decide, zero_mul, zero_add]

private theorem even_zmod_six_neg (a : ZMod 6) : Even (-a).val ↔ Even a.val := by
  fin_cases a <;> decide

private theorem even_zmod_six_intCast (n : ℤ) : Even (n : ZMod 6).val ↔ Even n := by
  have he : (((n : ZMod 6).val : ℕ) : ZMod 2) = (n : ZMod 2) := by
    rw [ZMod.natCast_val, ZMod.cast_intCast (by norm_num : 2 ∣ 6)]
  rw [even_iff_two_dvd, even_iff_two_dvd,
    ← ZMod.natCast_zmod_eq_zero_iff_dvd, he, ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num

/-- The beta lattice weight, including the factor nine on even first coordinates. -/
noncomputable def betaCubicWeight (a : Fin 2 → ZMod 6) : ℂ :=
  (cubicResidueCharacter (a 0) : ℂ) * if Even (a 0).val then 9 else 1

/-- The gamma lattice weight, supported on first coordinate three modulo six. -/
noncomputable def gammaCubicWeight (a : Fin 2 → ZMod 6) : ℂ :=
  if a 0 = 3 then (cubicResidueCharacter (a 1) : ℂ) else 0

theorem betaCubicWeight_intCast (v : Fin 2 → ℤ) :
    betaCubicWeight (fun i => (v i : ZMod 6)) =
      (legendreSym 3 (v 0) : ℂ) * if Even (v 0) then 9 else 1 := by
  simp only [betaCubicWeight, cubicResidueCharacter_intCast, even_zmod_six_intCast]

theorem gammaCubicWeight_intCast (v : Fin 2 → ℤ) :
    gammaCubicWeight (fun i => (v i : ZMod 6)) =
      if (v 0 : ZMod 6) = 3 then (legendreSym 3 (v 1) : ℂ) else 0 := by
  simp only [gammaCubicWeight, cubicResidueCharacter_intCast]

theorem betaCubicWeight_neg (a : Fin 2 → ZMod 6) :
    betaCubicWeight (-a) = -betaCubicWeight a := by
  simp only [betaCubicWeight, Pi.neg_apply, cubicResidueCharacter_neg,
    Int.cast_neg, even_zmod_six_neg, neg_mul]

theorem gammaCubicWeight_neg (a : Fin 2 → ZMod 6) :
    gammaCubicWeight (-a) = -gammaCubicWeight a := by
  have he : -(a 0) = (3 : ZMod 6) ↔ a 0 = 3 := by
    rw [neg_eq_iff_eq_neg, show -(3 : ZMod 6) = 3 by decide]
  simp only [gammaCubicWeight, Pi.neg_apply, he, cubicResidueCharacter_neg, Int.cast_neg]
  split_ifs <;> simp

theorem betaCubicWeight_zero_left {a : Fin 2 → ZMod 6} (ha : a 0 = 0) :
    betaCubicWeight a = 0 := by
  simp only [betaCubicWeight, ha, cubicResidueCharacter_zero, Int.cast_zero, zero_mul]

theorem gammaCubicWeight_zero_left {a : Fin 2 → ZMod 6} (ha : a 0 = 0) :
    gammaCubicWeight a = 0 := by
  simp only [gammaCubicWeight, ha, show (0 : ZMod 6) ≠ 3 by decide, if_false]

private theorem gamma0_six_diagonal {A : SL(2, ℤ)} (hA : A ∈ Gamma0 6) :
    ((A 0 0 : ZMod 6) = 1 ∧ (A 1 1 : ZMod 6) = 1) ∨
      ((A 0 0 : ZMod 6) = -1 ∧ (A 1 1 : ZMod 6) = -1) := by
  have hd : (A 0 0 : ZMod 6) * (A 1 1 : ZMod 6) = 1 := by
    have h : ((A : Matrix (Fin 2) (Fin 2) ℤ).det : ZMod 6) = 1 := by
      simp only [SpecialLinearGroup.det_coe, Int.cast_one]
    simpa only [Matrix.det_fin_two, Int.cast_sub, Int.cast_mul, Gamma0_mem.mp hA,
      mul_zero, sub_zero] using h
  have hf : ∀ a d : ZMod 6, a * d = 1 →
      (a = 1 ∧ d = 1) ∨ (a = -1 ∧ d = -1) := by decide
  exact hf _ _ hd

theorem cubicResidueCharacter_Gamma0_diagonal_eq {A : SL(2, ℤ)} (hA : A ∈ Gamma0 6) :
    cubicResidueCharacter (A 0 0 : ZMod 6) = cubicResidueCharacter (A 1 1 : ZMod 6) := by
  rcases gamma0_six_diagonal hA with ⟨ha, hd⟩ | ⟨ha, hd⟩ <;> rw [ha, hd]

theorem cubicResidueCharacter_Gamma0_sq {A : SL(2, ℤ)} (hA : A ∈ Gamma0 6) :
    cubicResidueCharacter (A 1 1 : ZMod 6) ^ 2 = 1 := by
  rcases gamma0_six_diagonal hA with ⟨_, hd⟩ | ⟨_, hd⟩ <;> simp [hd]

theorem cubicResidueCharacter_Gamma0_inv {A : SL(2, ℤ)} (hA : A ∈ Gamma0 6) :
    cubicResidueCharacter (A⁻¹ 1 1 : ZMod 6) = cubicResidueCharacter (A 1 1 : ZMod 6) := by
  rw [SpecialLinearGroup.SL2_inv_expl]
  exact cubicResidueCharacter_Gamma0_diagonal_eq hA

theorem betaCubicWeight_vecMul (a : Fin 2 → ZMod 6) {A : SL(2, ℤ)}
    (hA : A ∈ Gamma0 6) :
    betaCubicWeight (a ᵥ* (A : SL(2, ZMod 6))) =
      (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) * betaCubicWeight a := by
  have hc := Gamma0_mem.mp hA
  rcases gamma0_six_diagonal hA with ⟨ha, hd⟩ | ⟨ha, hd⟩ <;>
    simp [betaCubicWeight, Matrix.vecMul, Matrix.vec2_dotProduct, ha, hc, hd,
      even_zmod_six_neg]

theorem gammaCubicWeight_vecMul (a : Fin 2 → ZMod 6) {A : SL(2, ℤ)}
    (hA : A ∈ Gamma0 6) :
    gammaCubicWeight (a ᵥ* (A : SL(2, ZMod 6))) =
      (cubicResidueCharacter (A 1 1 : ZMod 6) : ℂ) * gammaCubicWeight a := by
  have hc := Gamma0_mem.mp hA
  have he : -(a 0) = (3 : ZMod 6) ↔ a 0 = 3 := by
    rw [neg_eq_iff_eq_neg, show -(3 : ZMod 6) = 3 by decide]
  rcases gamma0_six_diagonal hA with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · simp only [gammaCubicWeight, Matrix.vecMul, Matrix.vec2_dotProduct,
      SpecialLinearGroup.coe_matrix_coe, Matrix.map_apply, Int.coe_castRingHom,
      ha, hd, hc, mul_one, mul_zero, add_zero, cubicResidueCharacter_one, Int.cast_one, one_mul]
    split_ifs with h
    · rw [h, cubicResidueCharacter_three_mul_add]
    · rfl
  · simp only [gammaCubicWeight, Matrix.vecMul, Matrix.vec2_dotProduct,
      SpecialLinearGroup.coe_matrix_coe, Matrix.map_apply, Int.coe_castRingHom,
      ha, hd, hc, mul_neg_one, mul_zero, add_zero, he, cubicResidueCharacter_neg_one,
      Int.cast_neg, Int.cast_one, neg_one_mul]
    split_ifs with h
    · rw [h, cubicResidueCharacter_three_mul_add, cubicResidueCharacter_neg, Int.cast_neg]
    · simp

end DirichletL
