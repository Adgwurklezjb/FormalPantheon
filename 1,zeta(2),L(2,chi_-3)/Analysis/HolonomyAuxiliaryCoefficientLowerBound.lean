import Analysis.AuxiliaryCoefficientRate
import Analysis.AuxiliaryMinimalExponent

/-!
The actual auxiliary construction with a uniform arithmetic lower bound for
every minimum coefficient, CDT v2 TeX 3965-3998 and 4304-4518. Meanings and
the coefficient-selection quantifiers precede this proof in
-/

namespace DirichletL

open Filter

theorem exists_cdtAuxiliaryFormalSeries_minimum_coefficient_lower_bound (a b c : ℤ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ ε' δ : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 ∧ 0 < δ ∧ δ < ε' ∧ δ < 14 ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop, ∀ L : ℕ,
        (14 + δ) * D ≤ L → (L : ℝ) ≤ (14 + δ) * D + 1 →
        ∃ t : ↥(auxiliaryFreeIndices 14 h D ε') → ℤ,
          t ≠ 0 ∧ (∀ p, |(t p : ℝ)| ≤ Real.exp (ζ * (14 * h : ℕ) * D)) ∧
          auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε' t ≠ 0 ∧
          ∀ n : Fin (14 * h) →₀ ℕ,
            MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε' t) ≠ 0 →
            (∀ e : Fin (14 * h) →₀ ℕ, e.degree < n.degree →
              MvPowerSeries.coeff (R := ℚ) e
                (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε' t) = 0) →
            (∀ j, n j < L) ∧
            HasIntervalDiscrepancyLE (fun j => (n j : ℝ) / ((14 + δ) * D)) ε' ∧
            (∃ j, (14 - δ) * D < (n j : ℝ)) ∧
            -Real.log |(MvPowerSeries.coeff (R := ℚ) n
              (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε' t) : ℝ)| ≤
              98 * (h : ℝ) * D * ((16603 / 3920 : ℝ) + η) := by
  obtain ⟨ε₀, hε₀, hε₀1, hrate⟩ :=
    exists_epsilon_eventually_neg_log_abs_cdtAuxiliary_coeff_le a b c hη
  let ε' := min ε ε₀
  have hε' : 0 < ε' := lt_min hε hε₀
  obtain ⟨δ, hδ, hδε', hδm, hconstruction⟩ :=
    exists_cdtAuxiliaryFormalSeries_small_vanishing a b c hrel hne hε'
  have hcube := eventually_minimal_exponent_lt_cdtAuxiliaryFormalSeries
    (a : ℚ) (b : ℚ) (c : ℚ) hδ
  refine ⟨ε', δ, hε', min_le_left _ _, (min_le_right _ _).trans hε₀1,
    hδ, hδε', hδm, ?_⟩
  intro ζ hζ
  filter_upwards [hconstruction ζ hζ, hrate] with h hconstructionH hrateH
  filter_upwards [hconstructionH, hrateH, hcube] with D hconstructionD hrateD hcubeD
  intro L hRL hLR
  obtain ⟨t, ht, hsize, hF, hzero⟩ := hconstructionD L hRL hLR
  refine ⟨t, ht, hsize, hF, ?_⟩
  intro n hn hmin
  have hnL := hcubeD L hRL h ε' t n hn hmin
  obtain ⟨hdis, hlarge⟩ := minimal_exponent_avoids_auxiliary_constraints
    ((14 + δ) * D) ((14 - δ) * D) ε'
    (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε' t) n hn hnL hzero
  exact ⟨hnL, hdis, hlarge,
    hrateD ε' hε' (min_le_right _ _) δ hδ hδε' L hLR t n hnL hdis hn⟩

end DirichletL
