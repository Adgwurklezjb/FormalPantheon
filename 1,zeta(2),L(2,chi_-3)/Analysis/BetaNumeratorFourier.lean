import Analysis.BetaCubicFourier
import Analysis.DivisorSeries
import Arithmetic.Denominators

/-!
Identification of the beta lattice Fourier series with the literal divisor
numerator in CDT v2, Section 11.1, and Zagier (2009), Section 6.
-/

namespace DirichletL

open scoped UpperHalfPlane

/-- The base beta cubic term on the full natural product, with both axes zero. -/
private noncomputable def betaCubicBaseTerm (q : ℂ) (p : ℕ × ℕ) : ℂ :=
  (chiMinusThreeInt p.1 : ℂ) * (p.2 : ℂ) ^ 2 * q ^ (p.1 * p.2)

/-- The sum of the base beta cubic terms. -/
private noncomputable def betaCubicBaseSeries (q : ℂ) : ℂ := ∑' p, betaCubicBaseTerm q p

private theorem summable_betaCubicBaseTerm {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (betaCubicBaseTerm q) := by
  have hp := summable_cubicDoubleSeries_of_bounded
    (fun c _ => (chiMinusThreeInt c : ℂ)) (M := 1) (by norm_num)
    (fun c _ => norm_chiMinusThreeInt_complex_le_one c) hq
  exact ((hasSum_natProd_succ_iff (f := fun c r => betaCubicBaseTerm q (c, r))
    (by intro r; simp [betaCubicBaseTerm, chiMinusThreeInt_zero])
    (by intro c; simp [betaCubicBaseTerm])).mp hp.hasSum).summable

private theorem tsum_even_first (f : ℕ × ℕ → ℂ) :
    (∑' p : ℕ × ℕ, if Even p.1 then f p else 0) = ∑' p : ℕ × ℕ, f (2 * p.1, p.2) := by
  have hi : Function.Injective (fun p : ℕ × ℕ => (2 * p.1, p.2)) := by
    rintro ⟨c, r⟩ ⟨d, s⟩ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (by dsimp at h₁; omega) h₂
  have hs : Function.support (fun p : ℕ × ℕ => if Even p.1 then f p else 0) ⊆
      Set.range (fun p : ℕ × ℕ => (2 * p.1, p.2)) := by
    rintro ⟨c, r⟩ hp
    have he : Even c := by
      by_contra hn
      exact hp (by simp [hn])
    obtain ⟨n, hn⟩ := he
    exact ⟨(n, r), Prod.ext (by dsimp; omega) rfl⟩
  simpa [even_iff_two_dvd] using (hi.tsum_eq hs).symm

private theorem tsum_even_second (f : ℕ × ℕ → ℂ) :
    (∑' p : ℕ × ℕ, if Even p.2 then f p else 0) = ∑' p : ℕ × ℕ, f (p.1, 2 * p.2) := by
  have h := tsum_even_first (fun p => f (p.2, p.1))
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq] at h
  convert h using 1
  exact ((Equiv.prodComm ℕ ℕ).tsum_eq (fun p => f (p.1, 2 * p.2))).symm

private theorem betaCubicBaseSeries_even_first (q : ℂ) :
    (∑' p : ℕ × ℕ, if Even p.1 then betaCubicBaseTerm q p else 0) =
      -betaCubicBaseSeries (q ^ 2) := by
  rw [tsum_even_first, betaCubicBaseSeries, ← tsum_neg]
  apply tsum_congr
  rintro ⟨c, r⟩
  simp only [betaCubicBaseTerm, chiMinusThreeInt_mul, chiMinusThreeInt_two,
    neg_one_mul, Int.cast_neg, ← pow_mul, neg_mul, one_mul, mul_assoc]

private theorem betaCubicBaseSeries_even_second (q : ℂ) :
    (∑' p : ℕ × ℕ, if Even p.2 then betaCubicBaseTerm q p else 0) =
      4 * betaCubicBaseSeries (q ^ 2) := by
  rw [tsum_even_second, betaCubicBaseSeries, ← tsum_mul_left]
  apply tsum_congr
  rintro ⟨c, r⟩
  simp only [betaCubicBaseTerm, Nat.cast_mul, Nat.cast_ofNat, ← pow_mul]
  rw [show c * (2 * r) = 2 * (c * r) by ring]
  ring

private theorem betaCubicDoubleSeries_eq_base {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' p : ℕ × ℕ,
      ((chiMinusThreeInt (p.1 + 1) : ℂ) * (if Even (p.1 + 1) then 9 else 1)) *
        ((p.2 + 1 : ℕ) : ℂ) ^ 2 * q ^ ((p.1 + 1) * (p.2 + 1))) =
      betaCubicBaseSeries q - 8 * betaCubicBaseSeries (q ^ 2) := by
  let g : ℕ → ℕ → ℂ := fun c r =>
    ((chiMinusThreeInt c : ℂ) * (if Even c then 9 else 1)) * (r : ℂ) ^ 2 * q ^ (c * r)
  have hp := (summable_norm_betaCubicDoubleSeries hq).of_norm.hasSum
  have hg := (hasSum_natProd_succ_iff (f := g)
    (by intro r; simp [g, chiMinusThreeInt_zero]) (by intro c; simp [g])).mp hp
  rw [← hg.tsum_eq]
  have hf := summable_betaCubicBaseTerm hq
  have he : Summable (fun p : ℕ × ℕ => if Even p.1 then betaCubicBaseTerm q p else 0) := by
    convert hf.indicator {p : ℕ × ℕ | Even p.1} using 1
    ext p
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  calc
    (∑' p : ℕ × ℕ, g p.1 p.2) =
        ∑' p : ℕ × ℕ, (betaCubicBaseTerm q p +
          8 * (if Even p.1 then betaCubicBaseTerm q p else 0)) := by
      apply tsum_congr
      intro p
      dsimp [g, betaCubicBaseTerm]
      split_ifs <;> ring
    _ = betaCubicBaseSeries q + 8 *
        ∑' p : ℕ × ℕ, if Even p.1 then betaCubicBaseTerm q p else 0 := by
      rw [hf.tsum_add (he.mul_left 8), tsum_mul_left]
      rfl
    _ = _ := by rw [betaCubicBaseSeries_even_first]; ring

theorem hasSum_betaNumerator_mul_pow_complex {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (betaNumerator n : ℂ) * q ^ n)
      ((∑' p : ℕ × ℕ, (chiMinusThreeInt p.1 : ℂ) * (p.2 : ℂ) ^ 2 * q ^ (p.1 * p.2)) -
        8 * ∑' p : ℕ × ℕ,
          (chiMinusThreeInt p.1 : ℂ) * (p.2 : ℂ) ^ 2 * (q ^ 2) ^ (p.1 * p.2)) := by
  let g : ℕ → ℕ → ℂ := fun c r =>
    (chiMinusThreeInt c : ℂ) * (-1 : ℂ) ^ (r - 1) * (r : ℂ) ^ 2 * q ^ (c * r)
  have hf := summable_betaCubicBaseTerm hq
  have he : Summable (fun p : ℕ × ℕ => if Even p.2 then betaCubicBaseTerm q p else 0) := by
    convert hf.indicator {p : ℕ × ℕ | Even p.2} using 1
    ext p
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hg : HasSum (fun p : ℕ × ℕ => g p.1 p.2)
      (betaCubicBaseSeries q - 8 * betaCubicBaseSeries (q ^ 2)) := by
    have h := hf.hasSum.sub (he.hasSum.mul_left 2)
    rw [betaCubicBaseSeries_even_second] at h
    convert h using 1
    · ext ⟨c, r⟩
      cases r with
      | zero => simp [g, betaCubicBaseTerm]
      | succ r =>
        simp only [g, betaCubicBaseTerm, Nat.succ_eq_add_one, Nat.add_sub_cancel,
          neg_one_pow_eq_ite, Nat.even_add_one]
        split_ifs <;> ring
    · dsimp [betaCubicBaseSeries]
      ring
  have hg' : HasSum (fun p : ℕ × ℕ => g p.2 p.1)
      (betaCubicBaseSeries q - 8 * betaCubicBaseSeries (q ^ 2)) :=
    ((Equiv.prodComm ℕ ℕ).hasSum_iff (f := fun p : ℕ × ℕ => g p.1 p.2)).mpr hg
  have hz₁ : ∀ c, g c 0 = 0 := by intro c; simp [g]
  have hz₂ : ∀ r, g 0 r = 0 := by intro r; simp [g, chiMinusThreeInt_zero]
  have hp := (hasSum_natProd_succ_iff (f := fun r c => g c r) hz₁ hz₂).mpr hg'
  have hdiv := hasSum_mul_divisors (f := fun r c => g c r) hp hz₁ hz₂
  convert hdiv using 1
  ext n
  simp only [betaNumerator, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  dsimp [g]
  rw [Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
  ring

theorem weightedCubicEisenstein_beta_eq_tsum (τ : ℍ) :
    weightedCubicEisenstein betaCubicWeight τ =
      8 * (Real.pi : ℂ) ^ 3 * Complex.I *
        ∑' n : ℕ, (betaNumerator n : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ n := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one τ
  rw [weightedCubicEisenstein_beta_eq_doubleSeries, betaCubicDoubleSeries_eq_base hq,
    (hasSum_betaNumerator_mul_pow_complex hq).tsum_eq]
  rfl

end DirichletL
