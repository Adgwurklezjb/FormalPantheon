import Analysis.WeightedCubicRows
import Analysis.ReciprocalCubeFourier
import Analysis.CubicDoubleSeries
import Arithmetic.CubicEisensteinWeights

/-!
The positive double-series Fourier expansion of the beta lattice sum.
CDT v2, Section 11.1, and Zagier (2009), Section 6; the normalization
-/

namespace DirichletL

open scoped UpperHalfPlane

theorem betaCubicWeight_nat (c : ℕ) (d : ℤ) :
    betaCubicWeight (fun i => (![(c : ℤ), d] i : ZMod 6)) =
      (chiMinusThreeInt c : ℂ) * if Even c then 9 else 1 := by
  rw [betaCubicWeight_intCast]
  simp only [Matrix.cons_val_zero, Int.even_coe_nat, chiMinusThreeInt]

theorem betaCubicRow_fourier (τ : ℍ) {c : ℕ} (hc : 0 < c) :
    weightedCubicRow betaCubicWeight τ c =
      4 * (Real.pi : ℂ) ^ 3 * Complex.I *
        ((chiMinusThreeInt c : ℂ) * if Even c then 9 else 1) *
        ∑' r : ℕ, (r : ℂ) ^ 2 *
          Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (c * r) := by
  rw [weightedCubicRow_eq_tsum]
  simp only [betaCubicWeight_nat, div_eq_mul_inv, Int.cast_natCast]
  rw [tsum_mul_left]
  have hz : 0 < ((c : ℂ) * τ).im := by
    simpa using mul_pos (show (0 : ℝ) < c by exact_mod_cast hc) τ.im_pos
  have he : Complex.exp (2 * Real.pi * Complex.I * ((c : ℂ) * τ)) =
      Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ c := by
    rw [show 2 * Real.pi * Complex.I * ((c : ℂ) * τ) =
      (c : ℂ) * (2 * Real.pi * Complex.I * τ) by ring, Complex.exp_nat_mul]
  have h := tsum_one_div_int_add_cube hz
  simp only [one_div, he, ← pow_mul] at h
  rw [h]
  ring

theorem summable_norm_betaCubicDoubleSeries {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun p : ℕ × ℕ =>
      ‖((chiMinusThreeInt (p.1 + 1) : ℂ) * (if Even (p.1 + 1) then 9 else 1)) *
        ((p.2 + 1 : ℕ) : ℂ) ^ 2 * q ^ ((p.1 + 1) * (p.2 + 1))‖) := by
  apply summable_norm_cubicDoubleSeries_of_bounded
    (fun c _ => (chiMinusThreeInt c : ℂ) * if Even c then 9 else 1) (M := 9) (by norm_num)
  · intro c r
    rw [norm_mul]
    have hf : ‖(if Even c then 9 else 1 : ℂ)‖ ≤ 9 := by split_ifs <;> norm_num
    exact (mul_le_mul (norm_chiMinusThreeInt_complex_le_one c) hf
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul 9)
  · exact hq

theorem weightedCubicEisenstein_beta_eq_doubleSeries (τ : ℍ) :
    weightedCubicEisenstein betaCubicWeight τ =
      8 * (Real.pi : ℂ) ^ 3 * Complex.I *
        ∑' p : ℕ × ℕ,
          ((chiMinusThreeInt (p.1 + 1) : ℂ) * (if Even (p.1 + 1) then 9 else 1)) *
            ((p.2 + 1 : ℕ) : ℂ) ^ 2 *
            Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^
              ((p.1 + 1) * (p.2 + 1)) := by
  let q := Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ))
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  rw [weightedCubicEisenstein_eq_two_mul_tsum_rows _ betaCubicWeight_neg
    (fun _ ha => betaCubicWeight_zero_left ha)]
  have hr (c : ℕ) : weightedCubicRow betaCubicWeight τ (c + 1) =
      4 * (Real.pi : ℂ) ^ 3 * Complex.I *
        ∑' r : ℕ,
          ((chiMinusThreeInt (c + 1) : ℂ) * (if Even (c + 1) then 9 else 1)) *
            ((r + 1 : ℕ) : ℂ) ^ 2 * q ^ ((c + 1) * (r + 1)) := by
    have hb := betaCubicRow_fourier τ (Nat.succ_pos c)
    have hs : Summable (fun r : ℕ => (r : ℂ) ^ 2 * q ^ ((c + 1) * r)) := by
      simpa only [pow_mul] using summable_pow_mul_geometric_of_norm_lt_one 2
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero c))
    have hz := hs.tsum_eq_zero_add
    simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] at hz
    convert hb using 1
    rw [hz, ← tsum_mul_left, ← tsum_mul_left]
    apply tsum_congr
    intro r
    push_cast
    ring
  simp_rw [hr]
  rw [tsum_mul_left, (summable_norm_betaCubicDoubleSeries hq).of_norm.tsum_prod]
  ring

end DirichletL
