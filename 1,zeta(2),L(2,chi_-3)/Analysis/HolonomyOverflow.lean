import Arithmetic.DenominatorOverflow
import Analysis.HolonomyFamily

/-!
Perturbed denominators for the literal fourteen functions, following CDT v2,
Remark `rem:overflow`, equation `taub`, and the application at `typesA`
(supplied TeX 3549-3564 and 8280-8331). These coefficient and finite-rate
identities do not assert the analytic holonomy inequality.
-/

namespace DirichletL

open Filter

/-- Increase each nonzero array entry by ε and preserve the zero entries. -/
noncomputable def cdtDenominator14Perturbed (ε : ℝ) (i j : ℕ) : ℝ :=
  (1 + ε / 2) * cdtDenominator14 i j

theorem cdtDenominator14Perturbed_apply (ε : ℝ) (i j : ℕ) :
    cdtDenominator14Perturbed ε i j =
      if cdtDenominator14 i j = 0 then 0 else 2 + ε := by
  unfold cdtDenominator14Perturbed cdtDenominator14
  split_ifs <;> norm_num at * <;> ring

/-- The coefficient multiplier for the perturbed array, without fixed offsets. -/
noncomputable def cdtHolonomyPerturbedMultiplier (ε : ℝ) (i : Fin 14) (n : ℕ) : ℕ :=
  n ^ cdtIntegrationExponents ((i : ℕ) + 1) *
    ∏ j ∈ Finset.range 2,
      lcmPrefix ⌊cdtDenominator14Perturbed ε ((i : ℕ) + 1) (j + 1) * (n : ℝ)⌋₊

theorem cdtHolonomyPerturbedMultiplier_eq (ε : ℝ) (i : Fin 14) (n : ℕ) :
    cdtHolonomyPerturbedMultiplier ε i n = n ^ cdtIntegrationExponents ((i : ℕ) + 1) *
      if i = 0 then 1 else if (i : ℕ) < 3 then lcmPrefix ⌊(2 + ε) * (n : ℝ)⌋₊
      else lcmPrefix ⌊(2 + ε) * (n : ℝ)⌋₊ ^ 2 := by
  have htwo : (1 + ε / 2) * 2 = 2 + ε := by ring
  fin_cases i <;>
    simp [cdtHolonomyPerturbedMultiplier, cdtDenominator14Perturbed,
      cdtDenominator14, Finset.prod_range_succ, htwo, lcmPrefix_zero, pow_two]

theorem eventually_cdtHolonomyClearingMultiplier_dvd {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ i : Fin 14,
      cdtHolonomyClearingMultiplier i n ∣ cdtHolonomyPerturbedMultiplier ε i n := by
  filter_upwards [eventually_nat_add_le_floor_mul 2 6 hε] with n hn
  norm_num only [Nat.cast_ofNat] at hn
  have hL := lcmPrefix_dvd hn
  have hL0 : lcmPrefix (2 * n) ∣ lcmPrefix ⌊(2 + ε) * (n : ℝ)⌋₊ :=
    lcmPrefix_dvd (by omega)
  intro i
  rw [cdtHolonomyClearingMultiplier, cdtHolonomyPerturbedMultiplier_eq]
  apply Nat.mul_dvd_mul_left
  split_ifs
  · exact dvd_rfl
  · exact hL0
  · exact pow_dvd_pow_of_dvd hL 2

theorem cdtHolonomyPerturbedMultiplier_pos (ε : ℝ) (i : Fin 14) {n : ℕ} (hn : 0 < n) :
    0 < cdtHolonomyPerturbedMultiplier ε i n := by
  apply Nat.mul_pos (pow_pos hn _)
  exact Finset.prod_pos (fun _ _ => lcmPrefix_pos _)

theorem exists_int_smul_cdtHolonomySeries_denominators (a b c : ℤ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℤ, M ≠ 0 ∧
      (∀ i : Fin 14, IsLocalization.IsInteger ℤ
        (PowerSeries.coeff (R := ℚ) 0 ((M : ℚ) • cdtHolonomySeries a b c i))) ∧
      ∀ (i : Fin 14) (n : ℕ), IsLocalization.IsInteger ℤ
        ((cdtHolonomyPerturbedMultiplier ε i n : ℚ) *
          PowerSeries.coeff (R := ℚ) n ((M : ℚ) • cdtHolonomySeries a b c i)) := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 14, IsLocalization.IsInteger ℤ
      ((cdtHolonomyPerturbedMultiplier ε i n : ℚ) *
        PowerSeries.coeff (R := ℚ) n (cdtHolonomySeries a b c i)) := by
    filter_upwards [eventually_cdtHolonomyClearingMultiplier_dvd hε] with n hn
    intro i
    exact isInteger_nat_mul_of_dvd (isInteger_cdtHolonomySeries a b c i n) (hn i)
  obtain ⟨M, hM, h0, hcoeff⟩ := exists_int_mul_isInteger_of_eventually
    (fun i n => PowerSeries.coeff (R := ℚ) n (cdtHolonomySeries a b c i))
    (cdtHolonomyPerturbedMultiplier ε) he
  refine ⟨M, hM, ?_, ?_⟩
  · simpa only [PowerSeries.coeff_smul, smul_eq_mul] using h0
  · simpa only [PowerSeries.coeff_smul, smul_eq_mul] using hcoeff

theorem holonomyRowSum_mul (b : ℕ → ℕ → ℝ) (s : ℝ) (r i : ℕ) :
    holonomyRowSum (fun i j => s * b i j) r i = s * holonomyRowSum b r i := by
  simp only [holonomyRowSum, Finset.mul_sum]

theorem tauFlat_mul (m r : ℕ) (b : ℕ → ℕ → ℝ) (s : ℝ) :
    tauFlat m r (fun i j => s * b i j) = s * tauFlat m r b := by
  unfold tauFlat
  simp_rw [holonomyRowSum_mul]
  have hs : (∑ i ∈ Finset.range m,
      (2 * (i : ℝ) + 1) * (s * holonomyRowSum b r (i + 1))) =
      s * ∑ i ∈ Finset.range m, (2 * (i : ℝ) + 1) * holonomyRowSum b r (i + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

theorem tauFlat_cdtDenominator14Perturbed (ε : ℝ) :
    tauFlat 14 2 (cdtDenominator14Perturbed ε) = 191 / 49 + (191 / 98) * ε := by
  change tauFlat 14 2 (fun i j => (1 + ε / 2) * cdtDenominator14 i j) = _
  rw [tauFlat_mul, tauFlat_cdtDenominator14]
  ring

theorem holonomyDenominatorRate_cdt14Perturbed_eq (ε : ℝ) :
    holonomyDenominatorRate 14 2 (cdtDenominator14Perturbed ε) cdtIntegrationExponents =
      holonomyDenominatorRate 14 2 cdtDenominator14 cdtIntegrationExponents + (191 / 98) * ε := by
  simp only [holonomyDenominatorRate, tauFlat_cdtDenominator14Perturbed, tauFlat_cdtDenominator14]
  ring

end DirichletL
