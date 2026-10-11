import Analysis.HolonomyZeroEstimate
import Analysis.PowerSeriesPolynomialSpan
import Analysis.PowerSeriesCoefficientSections
import Analysis.AuxiliaryFormalSeries

/-!
Every minimum-total-degree exponent in CDT's actual auxiliary template:
`lem_Shidlovsky` (TeX 2910-2935) and the construction at TeX 3965-3998.
Meanings and strict-cutoff checks precede these proofs in
-/

namespace DirichletL

open Filter
open scoped Classical

theorem minimal_exponent_lt_auxiliaryFormalSeries {m : ℕ}
    (f : Fin m → PowerSeries ℚ) (h D : ℕ) (ε : ℝ)
    (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) (N : ℕ) (hD : 0 < D)
    (hbound : ∀ P : Fin m → Polynomial ℚ, (∀ i, (P i).natDegree < D) →
      (∑ i, (P i : PowerSeries ℚ) * f i) ≠ 0 →
        (∑ i, (P i : PowerSeries ℚ) * f i).order < (N : ℕ∞))
    (n : Fin (m * h) →₀ ℕ)
    (hn : MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries f h D ε t) ≠ 0)
    (hmin : ∀ e : Fin (m * h) →₀ ℕ, e.degree < n.degree →
      MvPowerSeries.coeff (R := ℚ) e (auxiliaryFormalSeries f h D ε t) = 0) :
    ∀ j, n j < N := by
  let g : ↥(auxiliaryFreeIndices m h D ε) → Fin (m * h) → PowerSeries ℚ :=
    fun p j => PowerSeries.monomial (R := ℚ) (p.val.2 j).val 1 * f (p.val.1 j)
  let V := Submodule.span ℚ (Set.range (fun p : Fin m × Fin D =>
    PowerSeries.monomial (R := ℚ) p.2.val 1 * f p.1))
  have hg (p : ↥(auxiliaryFreeIndices m h D ε)) (j : Fin (m * h)) : g p j ∈ V :=
    Submodule.subset_span ⟨(p.val.1 j, p.val.2 j), rfl⟩
  have he : (∑ p, (t p : ℚ) • ∏ j, powerSeriesInVariable ℚ j (g p j)) =
      auxiliaryFormalSeries f h D ε t := by
    simp only [g, prod_powerSeriesInVariable_shift, auxiliaryFormalSeries, auxiliarySeriesTerm]
  apply minimal_exponent_lt_of_separated_series_order_bound g (fun p => (t p : ℚ))
    (fun _ => V) hg (fun _ => N)
    (fun _ u hu hne => order_lt_of_mem_shifted_span f D N hD hbound u hu hne) n
  · rwa [he]
  · rwa [he]

theorem exists_minimal_exponent_bound_cdtAuxiliaryFormalSeries (a b c : ℚ) :
    ∃ B : ℕ, ∀ (h D : ℕ) (ε : ℝ) (t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ), 0 < D →
      ∀ n : Fin (14 * h) →₀ ℕ,
      MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) ≠ 0 →
      (∀ e : Fin (14 * h) →₀ ℕ, e.degree < n.degree →
        MvPowerSeries.coeff (R := ℚ) e (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) = 0) →
      ∀ j, n j < 14 * D + B := by
  obtain ⟨B, hB⟩ := exists_linear_order_bound_cdtHolonomySeries a b c
  refine ⟨B, ?_⟩
  intro h D ε t hD n hn hmin
  exact minimal_exponent_lt_auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t
    (14 * D + B) hD (fun P hP hF => hB D P hD hP hF) n hn hmin

theorem eventually_minimal_exponent_lt_cdtAuxiliaryFormalSeries (a b c : ℚ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ D : ℕ in atTop, ∀ L : ℕ, (14 + δ) * D ≤ L →
      ∀ (h : ℕ) (ε : ℝ) (t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ)
        (n : Fin (14 * h) →₀ ℕ),
      MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) ≠ 0 →
      (∀ e : Fin (14 * h) →₀ ℕ, e.degree < n.degree →
        MvPowerSeries.coeff (R := ℚ) e (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) = 0) →
      ∀ j, n j < L := by
  obtain ⟨B, hB⟩ := exists_minimal_exponent_bound_cdtAuxiliaryFormalSeries a b c
  obtain ⟨D₀, hD₀⟩ := exists_nat_gt ((B : ℝ) / δ)
  filter_upwards [eventually_ge_atTop D₀, eventually_ge_atTop 1] with D hDD hD
  have hBD : (B : ℝ) < δ * D := by
    have h : (B : ℝ) / δ < D := hD₀.trans_le (by exact_mod_cast hDD)
    have hb := (div_lt_iff₀ hδ).mp h
    simpa only [mul_comm] using hb
  intro L hL h ε t n hn hmin j
  have hj := hB h D ε t hD n hn hmin j
  have hjR : (n j : ℝ) < 14 * (D : ℝ) + B := by exact_mod_cast hj
  have hnL : (n j : ℝ) < L := by nlinarith
  exact_mod_cast hnL

end DirichletL
