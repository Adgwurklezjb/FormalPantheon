import Analysis.WeightedCubicRows
import Analysis.TwistedCubicFourier
import Analysis.CubicDoubleSeries
import Arithmetic.CubicEisensteinWeights

/-!
The full gamma lattice Fourier expansion with odd positive first indices.
CDT v2, Section 11.1; the support and normalization ledger is
-/

namespace DirichletL

open scoped UpperHalfPlane

theorem gammaCubicRow_eq_zero (τ : ℍ) {c : ℕ} (hc : (c : ZMod 6) ≠ 3) :
    weightedCubicRow gammaCubicWeight τ c = 0 := by
  rw [weightedCubicRow_eq_tsum]
  simp only [gammaCubicWeight_intCast, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_natCast, hc, if_false, zero_div, tsum_zero]

theorem gammaCubicRow_fourier (τ : ℍ) (n : ℕ) :
    weightedCubicRow gammaCubicWeight τ (6 * n + 3 : ℕ) =
      (gammaCubicFourierConstant / 2) *
        ∑' r : ℕ, (chiMinusThreeInt r : ℂ) * (r : ℂ) ^ 2 *
          Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ ((2 * n + 1) * r) := by
  have hc : ((6 * n + 3 : ℕ) : ZMod 6) = 3 := by
    push_cast
    change (0 : ZMod 6) * (n : ZMod 6) + 3 = 3
    ring
  rw [weightedCubicRow_eq_tsum]
  simp only [gammaCubicWeight_intCast, Matrix.cons_val_zero, Matrix.cons_val_one,
    Int.cast_natCast, hc, if_true]
  have hd : ((6 * n + 3 : ℕ) : ℂ) * τ = 3 * (((2 * n + 1 : ℕ) : ℂ) * τ) := by
    push_cast
    ring
  have hz : 0 < (((2 * n + 1 : ℕ) : ℂ) * τ).im := by
    simpa using mul_pos (show (0 : ℝ) < (2 * n + 1 : ℕ) by positivity) τ.im_pos
  rw [hd, tsum_twistedCubicRow_fourier hz]
  have he : Complex.exp (2 * Real.pi * Complex.I * (((2 * n + 1 : ℕ) : ℂ) * τ)) =
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (2 * n + 1) := by
    rw [show 2 * Real.pi * Complex.I * (((2 * n + 1 : ℕ) : ℂ) * τ) =
      ((2 * n + 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I * τ) by ring,
      Complex.exp_nat_mul]
  simp only [he, ← pow_mul]

theorem summable_norm_gammaCubicDoubleSeries {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖(chiMinusThreeInt (p.2 + 1) : ℂ) * ((p.2 + 1 : ℕ) : ℂ) ^ 2 *
        q ^ ((2 * p.1 + 1) * (p.2 + 1))‖) := by
  have h := summable_norm_cubicDoubleSeries_of_bounded
    (fun _ r => (chiMinusThreeInt r : ℂ)) (M := 1) (by norm_num)
    (fun _ r => norm_chiMinusThreeInt_complex_le_one r) hq
  exact h.comp_injective (i := fun p : ℕ × ℕ => (2 * p.1, p.2)) (by
    rintro ⟨m, r⟩ ⟨n, s⟩ he
    have h₁ := congrArg Prod.fst he
    have h₂ := congrArg Prod.snd he
    exact Prod.ext (by dsimp at h₁; omega) h₂)

theorem weightedCubicEisenstein_gamma_eq_doubleSeries (τ : ℍ) :
    weightedCubicEisenstein gammaCubicWeight τ = gammaCubicFourierConstant *
      ∑' p : ℕ × ℕ,
        (chiMinusThreeInt (p.2 + 1) : ℂ) * ((p.2 + 1 : ℕ) : ℂ) ^ 2 *
          Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^
            ((2 * p.1 + 1) * (p.2 + 1)) := by
  let q := Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  have hz := gammaCubicRow_eq_zero τ (c := 0) (by decide)
  simp only [Nat.cast_zero] at hz
  have hN : Summable (fun c : ℕ => weightedCubicRow gammaCubicWeight τ c) :=
    (summable_weightedCubicRows gammaCubicWeight τ).comp_injective Nat.cast_injective
  have hshift := hN.tsum_eq_zero_add
  simp only [Nat.cast_zero, hz, zero_add, Nat.cast_add, Nat.cast_one] at hshift
  rw [weightedCubicEisenstein_eq_two_mul_tsum_rows _ gammaCubicWeight_neg
    (fun _ ha => gammaCubicWeight_zero_left ha), ← hshift]
  have hi : Function.Injective (fun n : ℕ => 6 * n + 3) := by
    intro n m h
    change 6 * n + 3 = 6 * m + 3 at h
    omega
  have hs : Function.support (fun c : ℕ => weightedCubicRow gammaCubicWeight τ c) ⊆
      Set.range (fun n : ℕ => 6 * n + 3) := by
    intro c hc
    have he : (c : ZMod 6) = 3 :=
      by_contradiction (fun h => hc (gammaCubicRow_eq_zero τ h))
    obtain ⟨n, hn⟩ := (ZMod.natCast_eq_iff 6 c 3).mp he
    change c = 3 + 6 * n at hn
    exact ⟨n, by change 6 * n + 3 = c; omega⟩
  rw [← hi.tsum_eq hs]
  have hr (n : ℕ) : weightedCubicRow gammaCubicWeight τ (6 * n + 3 : ℕ) =
      (gammaCubicFourierConstant / 2) *
        ∑' r : ℕ, (chiMinusThreeInt (r + 1) : ℂ) * ((r + 1 : ℕ) : ℂ) ^ 2 *
          q ^ ((2 * n + 1) * (r + 1)) := by
    have hp := (summable_norm_gammaCubicDoubleSeries hq).of_norm.prod_factor n
    have hall : Summable (fun r : ℕ => (chiMinusThreeInt r : ℂ) * (r : ℂ) ^ 2 *
        q ^ ((2 * n + 1) * r)) :=
      (summable_nat_add_iff (f := fun r : ℕ =>
        (chiMinusThreeInt r : ℂ) * (r : ℂ) ^ 2 * q ^ ((2 * n + 1) * r)) 1).mp hp
    have he := hall.tsum_eq_zero_add
    simp only [chiMinusThreeInt_zero, Int.cast_zero, zero_mul, zero_add] at he
    rw [gammaCubicRow_fourier]
    exact congrArg (fun x => gammaCubicFourierConstant / 2 * x) he
  simp_rw [hr]
  rw [tsum_mul_left, (summable_norm_gammaCubicDoubleSeries hq).of_norm.tsum_prod]
  ring

end DirichletL
