import Arithmetic.Denominators

/-!
Finite formal q-series for CDT v2 Section 11.1, lines 7660-7678.  The
even-index correction includes the source's factor `1/4`.  These algebraic
coefficient identities make no analytic convergence or evaluation claim.
-/

namespace DirichletL

/-- The uncorrected positive-index coefficient in CDT's Eichler integral C. -/
noncomputable def gammaBaseCoeff (m : ℕ) : ℚ :=
  ((∑ d ∈ m.divisors, chiMinusThreeInt d * (d : ℤ) ^ 2 : ℤ) : ℚ) / (m : ℚ) ^ 2

/-- The uncorrected coefficient convention has zero constant coefficient. -/
theorem gammaBaseCoeff_zero : gammaBaseCoeff 0 = 0 := by
  simp [gammaBaseCoeff]

/-- The real divisor formula underlying C in CDT v2, Section 11.1, line 7674. -/
theorem gammaBaseCoeff_cast_eq_divisorSum (m : ℕ) :
    (gammaBaseCoeff m : ℝ) =
      ∑ d ∈ m.divisors, chiMinusThree d / (((m / d : ℕ) : ℝ) ^ 2) := by
  simp only [gammaBaseCoeff, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_intCast, Rat.cast_pow,
    Rat.cast_natCast, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    chiMinusThreeInt_cast, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
  have hmd : (m : ℝ) = (d : ℝ) * ((m / d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)).symm
  rw [hmd]
  rw [mul_pow, mul_comm ((d : ℝ) ^ 2),
    mul_div_mul_right _ _ (pow_ne_zero 2 hd0)]

/-- A finite version of the two q-series defining CDT's Eichler integral C. -/
noncomputable def gammaSeriesPartial (N : ℕ) : PowerSeries ℚ :=
  (∑ n ∈ Finset.Icc 1 N, PowerSeries.monomial (R := ℚ) n (gammaBaseCoeff n)) -
    ∑ n ∈ Finset.Icc 1 N,
      PowerSeries.monomial (R := ℚ) (2 * n) ((1 / 4 : ℚ) * gammaBaseCoeff n)

private theorem coeff_gammaBasePartial {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (PowerSeries.coeff (R := ℚ) m)
      (∑ n ∈ Finset.Icc 1 N, PowerSeries.monomial (R := ℚ) n (gammaBaseCoeff n)) =
        gammaBaseCoeff m := by
  classical
  have hmem : m ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hm, hmN⟩
  rw [map_sum, Finset.sum_eq_single m]
  · simp [PowerSeries.coeff_monomial]
  · intro b hb hbm
    simp [PowerSeries.coeff_monomial, hbm.symm]
  · intro h
    exact (h hmem).elim

private theorem coeff_gammaCorrectionPartial {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (PowerSeries.coeff (R := ℚ) m)
      (∑ n ∈ Finset.Icc 1 N,
        PowerSeries.monomial (R := ℚ) (2 * n) ((1 / 4 : ℚ) * gammaBaseCoeff n)) =
      if Even m then (1 / 4 : ℚ) * gammaBaseCoeff (m / 2) else 0 := by
  classical
  by_cases heven : Even m
  · obtain ⟨r, hr⟩ := even_iff_two_dvd.mp heven
    have hrpos : 0 < r := by omega
    have hrN : r ≤ N := by omega
    have hmem : r ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨hrpos, hrN⟩
    have hdiv : m / 2 = r := Nat.div_eq_of_eq_mul_right (by norm_num) hr
    rw [if_pos heven, hdiv, map_sum, Finset.sum_eq_single r]
    · simp [PowerSeries.coeff_monomial, hr]
    · intro b hb hbr
      have hne : m ≠ 2 * b := by omega
      simp [PowerSeries.coeff_monomial, hne]
    · intro h
      exact (h hmem).elim
  · rw [if_neg heven, map_sum]
    apply Finset.sum_eq_zero
    intro n hn
    have hne : m ≠ 2 * n := by
      intro heq
      exact heven (even_iff_two_dvd.mpr ⟨n, heq⟩)
    simp [PowerSeries.coeff_monomial, hne]

/-- The retained positive-degree coefficients are the checked gamma family. -/
theorem coeff_gammaSeriesPartial {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (PowerSeries.coeff (R := ℚ) m) (gammaSeriesPartial N) = gammaCoeff m := by
  classical
  rw [gammaSeriesPartial, map_sub, coeff_gammaBasePartial hm hmN,
    coeff_gammaCorrectionPartial hm hmN]
  by_cases heven : Even m
  · obtain ⟨r, hr⟩ := even_iff_two_dvd.mp heven
    have hrpos : 0 < r := by omega
    have hdiv : m / 2 = r := Nat.div_eq_of_eq_mul_right (by norm_num) hr
    rw [if_pos heven]
    simp only [gammaBaseCoeff, gammaCoeff, gammaNumerator, if_pos heven,
      Int.cast_sub, hdiv]
    rw [hr]
    push_cast
    field_simp
    ring
  · simp only [if_neg heven, sub_zero, gammaBaseCoeff, gammaCoeff,
      gammaNumerator, Int.cast_sub, Int.cast_zero]

/-- The real even-index correction for C in CDT v2, Section 11.1, line 7674. -/
theorem gammaCoeff_cast_eq {m : ℕ} (hm : m ≠ 0) :
    (gammaCoeff m : ℝ) = (gammaBaseCoeff m : ℝ) -
      if Even m then (1 / 4 : ℝ) * (gammaBaseCoeff (m / 2) : ℝ) else 0 := by
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have h : gammaCoeff m = gammaBaseCoeff m -
      if Even m then (1 / 4 : ℚ) * gammaBaseCoeff (m / 2) else 0 := by
    rw [← coeff_gammaSeriesPartial hmpos (le_refl m), gammaSeriesPartial,
      map_sub, coeff_gammaBasePartial hmpos (le_refl m),
      coeff_gammaCorrectionPartial hmpos (le_refl m)]
  have hc := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at hc
  by_cases heven : Even m <;> simpa [heven] using hc

end DirichletL
