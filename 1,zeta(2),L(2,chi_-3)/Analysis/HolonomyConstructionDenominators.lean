import Analysis.HolonomyFamily
import Arithmetic.DenominatorOverflow

/-!
One common coefficient denominator for CDT's auxiliary construction,
supplied v2 TeX 3986-3995 and the fourteen-series array at 8280-8331.
The constant coefficients are cleared separately from positive degrees.
-/

namespace DirichletL

theorem cdtHolonomyClearingMultiplier_dvd_lcmPrefix_cube (i : Fin 14)
    {n L : ℕ} (hn : 0 < n) (hnL : n ≤ L) :
    cdtHolonomyClearingMultiplier i n ∣ lcmPrefix (2 * L + 6) ^ 3 := by
  have hnT : n ∣ lcmPrefix (2 * L + 6) := dvd_lcmPrefix hn (by omega)
  have he : n ^ cdtIntegrationExponents ((i : ℕ) + 1) ∣ lcmPrefix (2 * L + 6) := by
    unfold cdtIntegrationExponents
    split_ifs
    · simpa only [pow_one] using hnT
    · simp only [pow_zero, one_dvd]
  have hr : (if i = 0 then 1 else if (i : ℕ) < 3 then lcmPrefix (2 * n)
      else lcmPrefix (2 * n + 6) ^ 2) ∣ lcmPrefix (2 * L + 6) ^ 2 := by
    split_ifs
    · exact one_dvd _
    · exact (lcmPrefix_dvd (by omega : 2 * n ≤ 2 * L + 6)).trans
        (dvd_pow_self _ (by decide : 2 ≠ 0))
    · exact pow_dvd_pow_of_dvd (lcmPrefix_dvd (by omega)) 2
  have h := mul_dvd_mul he hr
  simpa only [cdtHolonomyClearingMultiplier, pow_succ', pow_zero, mul_one] using h

theorem exists_common_clearing_cdtHolonomySeries (a b c : ℤ) :
    ∃ M : ℤ, M ≠ 0 ∧ ∀ L : ℕ, ∀ i : Fin 14, ∀ n : ℕ, n ≤ L →
      IsLocalization.IsInteger ℤ ((M : ℚ) * (lcmPrefix (2 * L + 6) : ℚ) ^ 3 *
        PowerSeries.coeff (R := ℚ) n (cdtHolonomySeries a b c i)) := by
  obtain ⟨M, hM⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun i : Fin 14 => PowerSeries.coeff (R := ℚ) 0 (cdtHolonomySeries a b c i))
  have hzero (i : Fin 14) : IsLocalization.IsInteger ℤ
      (((M : ℤ) : ℚ) * PowerSeries.coeff (R := ℚ) 0 (cdtHolonomySeries a b c i)) := by
    simpa only [Algebra.smul_def] using hM i
  refine ⟨(M : ℤ), mem_nonZeroDivisors_iff_ne_zero.mp M.property, ?_⟩
  intro L i n hnL
  by_cases hn : n = 0
  · subst n
    have hT : IsLocalization.IsInteger ℤ ((lcmPrefix (2 * L + 6) : ℚ) ^ 3) :=
      ⟨(lcmPrefix (2 * L + 6) : ℤ) ^ 3, by simp⟩
    simpa only [mul_assoc, mul_left_comm] using IsLocalization.isInteger_mul hT (hzero i)
  · have hc := isInteger_nat_mul_of_dvd (isInteger_cdtHolonomySeries a b c i n)
      (cdtHolonomyClearingMultiplier_dvd_lcmPrefix_cube i (Nat.pos_of_ne_zero hn) hnL)
    have hi : IsLocalization.IsInteger ℤ (((M : ℤ) : ℚ)) := ⟨(M : ℤ), rfl⟩
    simpa only [Nat.cast_pow, mul_assoc] using IsLocalization.isInteger_mul hi hc

end DirichletL
