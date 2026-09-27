import Analysis.FormalProductDerivative
import Analysis.LambertSeries

/-!
The exact formal logarithmic derivative of the original Hauptmodul in CDT v2,
Section 11.1, equation `haupt` (TeX lines 7619-7637), also Zagier (2009),
No modular identification with the binomial A-series is asserted here.
-/

namespace DirichletL

/-- The logarithmic derivative contributed by one positive-index factor. -/
noncomputable def hauptFactorLogDerivative (i : ℕ) : PowerSeries ℤ :=
  -(4 • lambertLogFactor (i + 1)) - 8 • lambertLogFactor (6 * (i + 1)) +
    8 • lambertLogFactor (2 * (i + 1)) + 4 • lambertLogFactor (3 * (i + 1))

theorem powerSeriesEuler_hauptFactor (i : ℕ) :
    powerSeriesEuler ℤ (hauptFactor i) = hauptFactor i * hauptFactorLogDerivative i := by
  have hmul {a b c d : PowerSeries ℤ}
      (ha : powerSeriesEuler ℤ a = a * c) (hb : powerSeriesEuler ℤ b = b * d) :
      powerSeriesEuler ℤ (a * b) = a * b * (c + d) := by
    rw [Derivation.leibniz, ha, hb]
    simp only [smul_eq_mul]
    ring
  have h := hmul (hmul (hmul
    (powerSeriesEuler_pow_of_eq (powerSeriesEuler_one_sub_X_pow (by omega : 0 < i + 1)) 4)
    (powerSeriesEuler_pow_of_eq
      (powerSeriesEuler_one_sub_X_pow (by omega : 0 < 6 * (i + 1))) 8))
    (powerSeriesEuler_pow_of_eq
      (powerSeriesEuler_oneSubInv (by omega : 0 < 2 * (i + 1))) 8))
    (powerSeriesEuler_pow_of_eq
      (powerSeriesEuler_oneSubInv (by omega : 0 < 3 * (i + 1))) 4)
  rw [hauptFactor, h]
  simp only [hauptFactorLogDerivative, nsmul_eq_mul]
  ring

/-- The exact divisor-series expression for theta(hauptmodul)/hauptmodul. -/
noncomputable def hauptmodulLogDerivativeSeries : PowerSeries ℤ :=
  1 - 4 • sigmaOneSeries +
    16 • MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.X ^ 2) sigmaOneSeries +
    12 • MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.X ^ 3) sigmaOneSeries -
    48 • MvPowerSeries.subst (fun (_ : Unit) => PowerSeries.X ^ 6) sigmaOneSeries

theorem coeff_sum_hauptFactorLogDerivative {n N : ℕ} (hnN : n ≤ N) :
    (∑ i ∈ Finset.range (N + 1), PowerSeries.coeff (R := ℤ) n (hauptFactorLogDerivative i)) =
      PowerSeries.coeff (R := ℤ) n (hauptmodulLogDerivativeSeries - 1) := by
  have h1 : (∑ i ∈ Finset.range (N + 1),
      PowerSeries.coeff (R := ℤ) n (lambertLogFactor (i + 1))) =
      PowerSeries.coeff (R := ℤ) n sigmaOneSeries := by
    have h := coeff_sum_lambertLogFactor (k := 1) (by norm_num) hnN
    rw [coeff_subst_X_pow sigmaOneSeries (by norm_num : 0 < 1)] at h
    simpa using h
  have h2 := coeff_sum_lambertLogFactor (k := 2) (by norm_num) hnN
  have h3 := coeff_sum_lambertLogFactor (k := 3) (by norm_num) hnN
  have h6 := coeff_sum_lambertLogFactor (k := 6) (by norm_num) hnN
  simp only [hauptFactorLogDerivative, hauptmodulLogDerivativeSeries,
    map_add, map_sub, map_neg, map_nsmul]
  simp only [nsmul_eq_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  rw [h1, h2, h3, h6]
  ring

theorem powerSeriesEuler_hauptmodul :
    powerSeriesEuler ℤ hauptmodul = hauptmodul * hauptmodulLogDerivativeSeries := by
  have hprod : powerSeriesEuler ℤ (formalProduct hauptFactor) =
      formalProduct hauptFactor * (hauptmodulLogDerivativeSeries - 1) :=
    powerSeriesEuler_formalProduct dvd_hauptFactor_sub_one powerSeriesEuler_hauptFactor
      (fun _ _ h => (coeff_sum_hauptFactorLogDerivative h).symm)
  have hx : powerSeriesEuler ℤ PowerSeries.X = PowerSeries.X := by
    simpa using (powerSeriesEuler_X_pow (R := ℤ) 1)
  simp only [hauptmodul, Derivation.leibniz, hx, hprod, smul_eq_mul]
  ring

end DirichletL
