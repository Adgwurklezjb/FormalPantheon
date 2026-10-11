import Analysis.ZagierSecondDerivativeCoefficients
import Analysis.ZagierFormalQSeriesIdentity
import Arithmetic.Denominators

/-!
Exact coefficients for the beta/gamma numerator-square comparison in
CDT v2, Section 11.1, and Zagier (2009), Sections 5-6.
The coefficient, shift, and denominator ledger is in
-/

namespace DirichletL

theorem coeff_five_hauptmodul : PowerSeries.coeff (R := ℤ) 5 hauptmodul = 39 := by
  have h := coeffs_zagierHauptmodul
  simp only [Prod.mk.injEq, zagierHauptmodul] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hL : (PowerSeries.coeff (R := ℤ) 3 hauptmodulLogDerivativeSeries,
      PowerSeries.coeff (R := ℤ) 4 hauptmodulLogDerivativeSeries) = (-4, 20) := by
    simp only [hauptmodulLogDerivativeSeries, map_add, map_sub, map_nsmul,
      PowerSeries.coeff_one]
    repeat' rw [coeff_subst_X_pow sigmaOneSeries (by norm_num)]
    norm_num [coeff_sigmaOneSeries, ArithmeticFunction.sigma_one_apply, Nat.divisors]
    decide
  simp only [Prod.mk.injEq] at hL
  have he := congrArg (PowerSeries.coeff (R := ℤ) 5) powerSeriesEuler_hauptmodul
  rw [coeff_powerSeriesEuler, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_eq_map, Finset.sum_map] at he
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4,
    coeff_zero_hauptmodulLogDerivativeSeries, coeff_one_hauptmodulLogDerivativeSeries,
    coeff_two_hauptmodulLogDerivativeSeries, hL.1, hL.2] at he
  linarith

theorem trunc_five_hauptmodulShift : PowerSeries.trunc 5 hauptmodulShift =
    1 - 4 * Polynomial.X + 10 * Polynomial.X ^ 2 - 20 * Polynomial.X ^ 3 +
      39 * Polynomial.X ^ 4 := by
  have h := coeffs_zagierHauptmodul
  simp only [Prod.mk.injEq, zagierHauptmodul] at h
  obtain ⟨_, h1, h2, h3, h4⟩ := h
  norm_num [PowerSeries.trunc_succ, PowerSeries.trunc_zero, hauptmodulShift,
    h1, h2, h3, h4, coeff_five_hauptmodul, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem trunc_five_caseCN : PowerSeries.trunc 5 zagierCaseCN =
    1 - 12 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 3 + 54 * Polynomial.X ^ 4 := by
  have h := coeffs_zagierCaseCN
  simp only [Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  norm_num [PowerSeries.trunc_succ, PowerSeries.trunc_zero, h0, h1, h2, h3, h4,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem trunc_five_caseCD : PowerSeries.trunc 5 zagierCaseCD =
    1 - 6 * Polynomial.X + 9 * Polynomial.X ^ 2 + 10 * Polynomial.X ^ 3 -
      30 * Polynomial.X ^ 4 := by
  have h := coeffs_zagierCaseCD
  simp only [Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  norm_num [PowerSeries.trunc_succ, PowerSeries.trunc_zero, h0, h1, h2, h3, h4,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

/-- The beta square difference after clearing the cube of the eta-square denominator. -/
noncomputable def betaNumeratorClearedSeries : PowerSeries ℤ :=
  (PowerSeries.mk betaNumerator) ^ 2 * zagierCaseCD ^ 3 -
    hauptmodul ^ 2 * (1 - 10 * hauptmodul + 9 * hauptmodul ^ 2) ^ 2 * zagierCaseCN ^ 3

/-- The analogous denominator-cleared gamma square difference. -/
noncomputable def gammaNumeratorClearedSeries : PowerSeries ℤ :=
  (PowerSeries.mk gammaNumerator) ^ 2 * zagierCaseCD ^ 3 -
    hauptmodul ^ 2 * (1 - 9 * hauptmodul) ^ 2 * zagierCaseCN ^ 3

private noncomputable def numeratorShift (a : ℕ → ℤ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => a (n + 1))

private theorem numerator_eq_X_mul_shift (a : ℕ → ℤ) (h0 : a 0 = 0) :
    PowerSeries.mk a = PowerSeries.X * numeratorShift a := by
  simpa [numeratorShift, h0] using PowerSeries.eq_X_mul_shift_add_const (PowerSeries.mk a)

private theorem trunc_five_betaShift : PowerSeries.trunc 5 (numeratorShift betaNumerator) =
    1 - 5 * Polynomial.X + 9 * Polynomial.X ^ 2 - 11 * Polynomial.X ^ 3 +
      24 * Polynomial.X ^ 4 := by
  norm_num [PowerSeries.trunc_succ, PowerSeries.trunc_zero, numeratorShift,
    betaNumerator_one, betaNumerator_two, betaNumerator_three, betaNumerator_four,
    betaNumerator_five, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

private theorem trunc_five_gammaShift : PowerSeries.trunc 5 (numeratorShift gammaNumerator) =
    1 - 4 * Polynomial.X + Polynomial.X ^ 2 + 16 * Polynomial.X ^ 3 -
      24 * Polynomial.X ^ 4 := by
  have h : (gammaNumerator 1, gammaNumerator 2, gammaNumerator 3,
      gammaNumerator 4, gammaNumerator 5) = (1, -4, 1, 16, -24) := by decide
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  norm_num [PowerSeries.trunc_succ, PowerSeries.trunc_zero, numeratorShift,
    h1, h2, h3, h4, h5, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

private theorem mk_eq_trunc (n : ℕ) (f : PowerSeries ℤ) :
    Ideal.Quotient.mk (Ideal.span ({PowerSeries.X ^ n} : Set (PowerSeries ℤ))) f =
      Ideal.Quotient.mk (Ideal.span ({PowerSeries.X ^ n} : Set (PowerSeries ℤ)))
        (PowerSeries.trunc n f) := by
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro m hm
  simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hm]

set_option maxHeartbeats 600000 in
private theorem beta_shifted_difference_dvd : (PowerSeries.X : PowerSeries ℤ) ^ 5 ∣
    numeratorShift betaNumerator ^ 2 * zagierCaseCD ^ 3 -
      hauptmodulShift ^ 2 *
        (1 - 10 * (PowerSeries.X * hauptmodulShift) +
          9 * (PowerSeries.X * hauptmodulShift) ^ 2) ^ 2 * zagierCaseCN ^ 3 := by
  let J : Ideal (PowerSeries ℤ) := Ideal.span {PowerSeries.X ^ 5}
  let π := Ideal.Quotient.mk J
  let x := π PowerSeries.X
  have hx : Polynomial.coeToPowerSeries.ringHom (Polynomial.X : Polynomial ℤ) =
      (PowerSeries.X : PowerSeries ℤ) := Polynomial.coe_X
  have hX : x ^ 5 = 0 := by
    rw [show x ^ 5 = π (PowerSeries.X ^ 5) from (map_pow π _ _).symm]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hp (n : ℕ) (hn : 5 ≤ n) : x ^ n = 0 := pow_eq_zero_of_le hn hX
  have hH : π hauptmodulShift = 1 - 4 * x + 10 * x ^ 2 - 20 * x ^ 3 + 39 * x ^ 4 := by
    calc
      π hauptmodulShift = π (PowerSeries.trunc 5 hauptmodulShift) := mk_eq_trunc 5 hauptmodulShift
      _ = _ := by
        rw [trunc_five_hauptmodulShift]
        simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub,
          map_mul, map_pow, map_natCast, map_ofNat, map_one, hx]
        rfl
  have hN : π zagierCaseCN = 1 - 12 * x ^ 2 - 2 * x ^ 3 + 54 * x ^ 4 := by
    calc
      π zagierCaseCN = π (PowerSeries.trunc 5 zagierCaseCN) := mk_eq_trunc 5 zagierCaseCN
      _ = _ := by
        rw [trunc_five_caseCN]
        simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub,
          map_mul, map_pow, map_natCast, map_ofNat, map_one, hx]
        rfl
  have hD : π zagierCaseCD = 1 - 6 * x + 9 * x ^ 2 + 10 * x ^ 3 - 30 * x ^ 4 := by
    calc
      π zagierCaseCD = π (PowerSeries.trunc 5 zagierCaseCD) := mk_eq_trunc 5 zagierCaseCD
      _ = _ := by
        rw [trunc_five_caseCD]
        simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub,
          map_mul, map_pow, map_natCast, map_ofNat, map_one, hx]
        rfl
  have hB : π (numeratorShift betaNumerator) =
      1 - 5 * x + 9 * x ^ 2 - 11 * x ^ 3 + 24 * x ^ 4 := by
    calc
      π (numeratorShift betaNumerator) = π (PowerSeries.trunc 5 (numeratorShift betaNumerator)) :=
        mk_eq_trunc 5 (numeratorShift betaNumerator)
      _ = _ := by
        rw [trunc_five_betaShift]
        simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub,
          map_mul, map_pow, map_natCast, map_ofNat, map_one, hx]
        rfl
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
  change π _ = 0
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, hH, hN, hD, hB]
  change (1 - 5 * x + 9 * x ^ 2 - 11 * x ^ 3 + 24 * x ^ 4) ^ 2 *
      (1 - 6 * x + 9 * x ^ 2 + 10 * x ^ 3 - 30 * x ^ 4) ^ 3 -
    (1 - 4 * x + 10 * x ^ 2 - 20 * x ^ 3 + 39 * x ^ 4) ^ 2 *
      (1 - 10 * (x * (1 - 4 * x + 10 * x ^ 2 - 20 * x ^ 3 + 39 * x ^ 4)) +
        9 * (x * (1 - 4 * x + 10 * x ^ 2 - 20 * x ^ 3 + 39 * x ^ 4)) ^ 2) ^ 2 *
      (1 - 12 * x ^ 2 - 2 * x ^ 3 + 54 * x ^ 4) ^ 3 = 0
  ring_nf
  norm_num [hp]

set_option maxHeartbeats 400000 in
private theorem gamma_shifted_difference_dvd : (PowerSeries.X : PowerSeries ℤ) ^ 5 ∣
    numeratorShift gammaNumerator ^ 2 * zagierCaseCD ^ 3 -
      hauptmodulShift ^ 2 * (1 - 9 * (PowerSeries.X * hauptmodulShift)) ^ 2 *
        zagierCaseCN ^ 3 := by
  let J : Ideal (PowerSeries ℤ) := Ideal.span {PowerSeries.X ^ 5}
  let π := Ideal.Quotient.mk J
  let x := π PowerSeries.X
  have hx : Polynomial.coeToPowerSeries.ringHom (Polynomial.X : Polynomial ℤ) =
      (PowerSeries.X : PowerSeries ℤ) := Polynomial.coe_X
  have hX : x ^ 5 = 0 := by
    rw [show x ^ 5 = π (PowerSeries.X ^ 5) from (map_pow π _ _).symm]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hp (n : ℕ) (hn : 5 ≤ n) : x ^ n = 0 := pow_eq_zero_of_le hn hX
  have hH : π hauptmodulShift = 1 - 4 * x + 10 * x ^ 2 - 20 * x ^ 3 + 39 * x ^ 4 := by
    calc
      π hauptmodulShift = π (PowerSeries.trunc 5 hauptmodulShift) := mk_eq_trunc 5 hauptmodulShift
      _ = _ := by
        rw [trunc_five_hauptmodulShift]
        simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub,
          map_mul, map_pow, map_natCast, map_ofNat, map_one, hx]
        rfl
  have hN : π zagierCaseCN = 1 - 12 * x ^ 2 - 2 * x ^ 3 + 54 * x ^ 4 := by
    calc
      π zagierCaseCN = π (PowerSeries.trunc 5 zagierCaseCN) := mk_eq_trunc 5 zagierCaseCN
      _ = _ := by
        rw [trunc_five_caseCN]
        simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub,
          map_mul, map_pow, map_natCast, map_ofNat, map_one, hx]
        rfl
  have hD : π zagierCaseCD = 1 - 6 * x + 9 * x ^ 2 + 10 * x ^ 3 - 30 * x ^ 4 := by
    calc
      π zagierCaseCD = π (PowerSeries.trunc 5 zagierCaseCD) := mk_eq_trunc 5 zagierCaseCD
      _ = _ := by
        rw [trunc_five_caseCD]
        simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub,
          map_mul, map_pow, map_natCast, map_ofNat, map_one, hx]
        rfl
  have hB : π (numeratorShift gammaNumerator) =
      1 - 4 * x + x ^ 2 + 16 * x ^ 3 - 24 * x ^ 4 := by
    calc
      π (numeratorShift gammaNumerator) = π (PowerSeries.trunc 5 (numeratorShift gammaNumerator)) :=
        mk_eq_trunc 5 (numeratorShift gammaNumerator)
      _ = _ := by
        rw [trunc_five_gammaShift]
        simp only [← Polynomial.coeToPowerSeries.ringHom_apply, map_add, map_sub,
          map_mul, map_pow, map_natCast, map_ofNat, map_one, hx]
        rfl
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
  change π _ = 0
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, hH, hN, hD, hB]
  change (1 - 4 * x + x ^ 2 + 16 * x ^ 3 - 24 * x ^ 4) ^ 2 *
      (1 - 6 * x + 9 * x ^ 2 + 10 * x ^ 3 - 30 * x ^ 4) ^ 3 -
    (1 - 4 * x + 10 * x ^ 2 - 20 * x ^ 3 + 39 * x ^ 4) ^ 2 *
      (1 - 9 * (x * (1 - 4 * x + 10 * x ^ 2 - 20 * x ^ 3 + 39 * x ^ 4))) ^ 2 *
      (1 - 12 * x ^ 2 - 2 * x ^ 3 + 54 * x ^ 4) ^ 3 = 0
  ring_nf
  norm_num [hp]

theorem coeff_zero_betaNumeratorClearedSeries (m : ℕ) (hm : m < 7) :
    PowerSeries.coeff (R := ℤ) m betaNumeratorClearedSeries = 0 := by
  apply (PowerSeries.X_pow_dvd_iff (n := 7)).mp ?_ m hm
  obtain ⟨r, hr⟩ := beta_shifted_difference_dvd
  refine ⟨r, ?_⟩
  rw [betaNumeratorClearedSeries,
    numerator_eq_X_mul_shift betaNumerator (by decide), hauptmodul_eq_X_mul_hauptmodulShift]
  calc
    _ = PowerSeries.X ^ 2 * (numeratorShift betaNumerator ^ 2 * zagierCaseCD ^ 3 -
      hauptmodulShift ^ 2 * (1 - 10 * (PowerSeries.X * hauptmodulShift) +
        9 * (PowerSeries.X * hauptmodulShift) ^ 2) ^ 2 * zagierCaseCN ^ 3) := by ring
    _ = PowerSeries.X ^ 7 * r := by rw [hr]; ring

theorem coeff_zero_gammaNumeratorClearedSeries (m : ℕ) (hm : m < 7) :
    PowerSeries.coeff (R := ℤ) m gammaNumeratorClearedSeries = 0 := by
  apply (PowerSeries.X_pow_dvd_iff (n := 7)).mp ?_ m hm
  obtain ⟨r, hr⟩ := gamma_shifted_difference_dvd
  refine ⟨r, ?_⟩
  rw [gammaNumeratorClearedSeries,
    numerator_eq_X_mul_shift gammaNumerator (by decide), hauptmodul_eq_X_mul_hauptmodulShift]
  calc
    _ = PowerSeries.X ^ 2 * (numeratorShift gammaNumerator ^ 2 * zagierCaseCD ^ 3 -
      hauptmodulShift ^ 2 * (1 - 9 * (PowerSeries.X * hauptmodulShift)) ^ 2 *
        zagierCaseCN ^ 3) := by ring
    _ = PowerSeries.X ^ 7 * r := by rw [hr]; ring

end DirichletL
