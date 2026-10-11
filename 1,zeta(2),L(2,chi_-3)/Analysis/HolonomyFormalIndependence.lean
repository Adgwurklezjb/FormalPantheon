import Analysis.HolonomyFamily

/-!
Formal independence over the canonical rational-function field, for CDT v2,
`main:elementary form` and its application (supplied TeX 3477-3540 and
8280-8331). Analytic polynomial relations transfer through the literal
expansions; Mathlib supplies the fraction-ring independence equivalence.
-/

namespace DirichletL

open Filter
open scoped Topology RatFunc

theorem eventually_polynomialRelation_of_powerSeriesRelation
    {ι : Type*} [Fintype ι] {p : ι → PowerSeries ℚ} {f : ι → ℂ → ℂ}
    (hf : ∀ i, HasFPowerSeriesAt (f i) (complexSeries (p i)) 0)
    (P : ι → Polynomial ℚ) (hP : ∑ i, (P i : PowerSeries ℚ) * p i = 0) :
    ∀ᶠ z : ℂ in 𝓝 0, ∑ i, Polynomial.aeval z (P i) * f i z = 0 := by
  filter_upwards [eventually_all.mpr (fun i => eventually_hasSum_of_hasFPowerSeriesAt (hf i))]
    with z hz
  have hs : HasSum
      (fun n : ℕ => ∑ i, (PowerSeries.coeff (R := ℚ) n ((P i : PowerSeries ℚ) * p i) : ℂ) * z ^ n)
      (∑ i, Polynomial.aeval z (P i) * f i z) :=
    hasSum_sum (fun i (_ : i ∈ Finset.univ) => hasSum_polynomial_mul (hz i) (P i))
  have he (n : ℕ) :
      (∑ i, (PowerSeries.coeff (R := ℚ) n ((P i : PowerSeries ℚ) * p i) : ℂ) * z ^ n) = 0 := by
    rw [← Finset.sum_mul, ← Rat.cast_sum, ← map_sum, hP, map_zero, Rat.cast_zero, zero_mul]
  exact (hs.congr_fun (fun n => (he n).symm)).unique hasSum_zero

theorem eq_zero_of_cdtFourteenSeriesPolynomialRelation (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) (P : Fin 14 → Polynomial ℚ)
    (hP : ∑ i, (P i : PowerSeries ℚ) * cdtFourteenSeries a b c i = 0) : P = 0 := by
  have he := eventually_polynomialRelation_of_powerSeriesRelation
    (hasFPowerSeriesAt_cdtFourteenFamily a b c hrel) P hP
  have hC := eq_zero_of_cdtFourteenPolynomialRelation a b c hrel hne
    (fun i => (P i).map (algebraMap ℚ ℂ)) (by
      filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
      simpa only [Polynomial.eval_map, ← Polynomial.aeval_def, Pi.zero_apply] using hz)
  funext i
  apply Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  simpa only [Polynomial.map_zero, Pi.zero_apply] using congrFun hC i

theorem linearIndependent_laurentSeries_of_polynomial_relation
    {ι : Type*} [Fintype ι] (p : ι → PowerSeries ℚ)
    (hp : ∀ P : ι → Polynomial ℚ,
      (∑ i, (P i : PowerSeries ℚ) * p i) = 0 → P = 0) :
    LinearIndependent (RatFunc ℚ) (fun i => (p i : LaurentSeries ℚ)) := by
  apply (LinearIndependent.iff_fractionRing (Polynomial ℚ) (RatFunc ℚ)).mp
  apply Fintype.linearIndependent_iff.mpr
  intro P hP i
  have hz : (∑ j, (P j : PowerSeries ℚ) * p j) = 0 := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ))
    rw [map_sum, map_zero]
    simpa only [map_mul, Algebra.smul_def, Polynomial.algebraMap_hahnSeries_apply] using hP
  exact congrFun (hp P hz) i

theorem linearIndependent_cdtFourteenSeries (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    LinearIndependent (RatFunc ℚ)
      (fun i : Fin 14 => (cdtFourteenSeries a b c i : LaurentSeries ℚ)) :=
  linearIndependent_laurentSeries_of_polynomial_relation (cdtFourteenSeries a b c)
    (eq_zero_of_cdtFourteenSeriesPolynomialRelation a b c hrel hne)

theorem linearIndependent_cdtHolonomySeries (a b c : ℚ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    LinearIndependent (RatFunc ℚ)
      (fun i : Fin 14 => (cdtHolonomySeries a b c i : LaurentSeries ℚ)) :=
  (linearIndependent_cdtFourteenSeries a b c hrel hne).comp
    cdtHolonomyOrder cdtHolonomyOrder_injective

end DirichletL
