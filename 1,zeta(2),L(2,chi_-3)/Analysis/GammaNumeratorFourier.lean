import Analysis.GammaCubicFourier
import Analysis.DivisorSeries
import Arithmetic.Denominators

/-!
The literal gamma divisor numerator and its even-index correction in
CDT v2, Section 11.1. The zero-axis and normalization checks are recorded
-/

namespace DirichletL

open scoped UpperHalfPlane

/-- The gamma cubic base term, explicitly excluding its nondecaying zero first axis. -/
private noncomputable def gammaCubicBaseTerm (q : ℂ) (p : ℕ × ℕ) : ℂ :=
  if p.1 = 0 then 0 else (chiMinusThreeInt p.2 : ℂ) * (p.2 : ℂ) ^ 2 * q ^ (p.1 * p.2)

/-- The full sum of the gamma base terms with both axes zero. -/
private noncomputable def gammaCubicBaseSeries (q : ℂ) : ℂ := ∑' p, gammaCubicBaseTerm q p

private theorem summable_gammaCubicBaseTerm {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (gammaCubicBaseTerm q) := by
  have hp := summable_cubicDoubleSeries_of_bounded
    (fun _ r => (chiMinusThreeInt r : ℂ)) (M := 1) (by norm_num)
    (fun _ r => norm_chiMinusThreeInt_complex_le_one r) hq
  have h : HasSum (fun p : ℕ × ℕ => gammaCubicBaseTerm q (p.1 + 1, p.2 + 1))
      (∑' p : ℕ × ℕ, (chiMinusThreeInt (p.2 + 1) : ℂ) * ((p.2 + 1 : ℕ) : ℂ) ^ 2 *
        q ^ ((p.1 + 1) * (p.2 + 1))) := by
    simpa [gammaCubicBaseTerm] using hp.hasSum
  exact ((hasSum_natProd_succ_iff (f := fun c r => gammaCubicBaseTerm q (c, r))
    (by intro r; simp [gammaCubicBaseTerm])
    (by intro c; simp [gammaCubicBaseTerm, chiMinusThreeInt_zero])).mp h).summable

private theorem gammaCubicBaseTerm_even_first (q : ℂ) (c r : ℕ) :
    gammaCubicBaseTerm q (2 * c, r) = gammaCubicBaseTerm (q ^ 2) (c, r) := by
  simp [gammaCubicBaseTerm, ← pow_mul, mul_assoc]

private theorem gammaCubicBaseSeries_even_first {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' c : ℕ, ∑' r : ℕ, gammaCubicBaseTerm q (2 * c, r)) =
      gammaCubicBaseSeries (q ^ 2) := by
  simp_rw [gammaCubicBaseTerm_even_first]
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by decide : 2 ≠ 0)
  exact (summable_gammaCubicBaseTerm hq2).tsum_prod.symm

private theorem gammaCubicDoubleSeries_eq_base {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' p : ℕ × ℕ, (chiMinusThreeInt (p.2 + 1) : ℂ) * ((p.2 + 1 : ℕ) : ℂ) ^ 2 *
      q ^ ((2 * p.1 + 1) * (p.2 + 1))) =
      gammaCubicBaseSeries q - gammaCubicBaseSeries (q ^ 2) := by
  have hf := summable_gammaCubicBaseTerm hq
  have hr := hf.prod
  have he := hr.comp_injective (i := fun c : ℕ => 2 * c) (by
    intro c d h
    change 2 * c = 2 * d at h
    omega)
  have ho := hr.comp_injective (i := fun c : ℕ => 2 * c + 1) (by
    intro c d h
    change 2 * c + 1 = 2 * d + 1 at h
    omega)
  have hsplit : (∑' c : ℕ, ∑' r : ℕ, gammaCubicBaseTerm q (2 * c, r)) +
      (∑' c : ℕ, ∑' r : ℕ, gammaCubicBaseTerm q (2 * c + 1, r)) =
        gammaCubicBaseSeries q := by
    exact (tsum_even_add_odd (f := fun c : ℕ => ∑' r : ℕ, gammaCubicBaseTerm q (c, r))
      he ho).trans hf.tsum_prod.symm
  rw [gammaCubicBaseSeries_even_first hq] at hsplit
  have hrow (c : ℕ) :
      (∑' r : ℕ, (chiMinusThreeInt (r + 1) : ℂ) * ((r + 1 : ℕ) : ℂ) ^ 2 *
        q ^ ((2 * c + 1) * (r + 1))) =
        ∑' r : ℕ, gammaCubicBaseTerm q (2 * c + 1, r) := by
    have h := (hf.prod_factor (2 * c + 1)).tsum_eq_zero_add
    simpa [gammaCubicBaseTerm, chiMinusThreeInt_zero] using h.symm
  rw [(summable_norm_gammaCubicDoubleSeries hq).of_norm.tsum_prod]
  simp_rw [hrow]
  linear_combination hsplit

private theorem hasSum_gammaCubicBaseNumerator {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ =>
      ((∑ d ∈ n.divisors, chiMinusThreeInt d * (d : ℤ) ^ 2 : ℤ) : ℂ) * q ^ n)
      (gammaCubicBaseSeries q) := by
  let f : ℕ → ℕ → ℂ := fun r c => gammaCubicBaseTerm q (c, r)
  have hf : HasSum (fun p : ℕ × ℕ => f p.1 p.2) (gammaCubicBaseSeries q) :=
    ((Equiv.prodComm ℕ ℕ).hasSum_iff (f := gammaCubicBaseTerm q)).mpr
      (summable_gammaCubicBaseTerm hq).hasSum
  have hz₁ : ∀ c, f 0 c = 0 := by intro c; simp [f, gammaCubicBaseTerm, chiMinusThreeInt_zero]
  have hz₂ : ∀ r, f r 0 = 0 := by intro r; simp [f, gammaCubicBaseTerm]
  have hp := (hasSum_natProd_succ_iff hz₁ hz₂).mpr hf
  have hd := hasSum_mul_divisors (f := f) hp hz₁ hz₂
  convert hd using 1
  ext n
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hn : n ≠ 0 := (Nat.mem_divisors.mp hd).2
  have hnd : n / d ≠ 0 := Nat.ne_of_gt (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd))
    (Nat.pos_of_mem_divisors hd))
  simp only [f, gammaCubicBaseTerm, hnd, if_false,
    Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]

theorem hasSum_gammaNumerator_mul_pow_complex {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (gammaNumerator n : ℂ) * q ^ n)
      ((∑' p : ℕ × ℕ, if p.1 = 0 then 0 else
        (chiMinusThreeInt p.2 : ℂ) * (p.2 : ℂ) ^ 2 * q ^ (p.1 * p.2)) -
      ∑' p : ℕ × ℕ, if p.1 = 0 then 0 else
        (chiMinusThreeInt p.2 : ℂ) * (p.2 : ℂ) ^ 2 * (q ^ 2) ^ (p.1 * p.2)) := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by decide : 2 ≠ 0)
  let g : ℕ → ℂ := fun n => if Even n then
    ((∑ d ∈ (n / 2).divisors, chiMinusThreeInt d * (d : ℤ) ^ 2 : ℤ) : ℂ) * q ^ n else 0
  have hi : Function.Injective (fun n : ℕ => 2 * n) := by
    intro n m h
    change 2 * n = 2 * m at h
    omega
  have hc : HasSum g (gammaCubicBaseSeries (q ^ 2)) := by
    apply (hi.hasSum_iff (f := g) ?_).mp
    · convert hasSum_gammaCubicBaseNumerator hq2 using 1
      ext n
      simp [g, even_iff_two_dvd, pow_mul]
    · intro n hn
      have he : ¬Even n := by
        rintro ⟨m, hm⟩
        exact hn ⟨m, by change 2 * m = n; omega⟩
      simp [g, he]
  have hs := (hasSum_gammaCubicBaseNumerator hq).sub hc
  convert hs using 1
  ext n
  by_cases hn : Even n <;> simp [gammaNumerator, g, hn, sub_mul]

theorem weightedCubicEisenstein_gamma_eq_tsum (τ : ℍ) :
    weightedCubicEisenstein gammaCubicWeight τ = gammaCubicFourierConstant *
      ∑' n : ℕ, (gammaNumerator n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  rw [weightedCubicEisenstein_gamma_eq_doubleSeries, gammaCubicDoubleSeries_eq_base hq,
    (hasSum_gammaNumerator_mul_pow_complex hq).tsum_eq]
  rfl

end DirichletL
