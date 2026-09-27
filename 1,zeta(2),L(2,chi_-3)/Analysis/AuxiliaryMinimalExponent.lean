import Analysis.AuxiliaryZeroEstimate
import Analysis.HolonomyAuxiliaryConstruction

/-!
A controlled coefficient of minimum total degree for CDT v2's auxiliary
construction, `lem_Shidlovsky` (TeX 2910-2935) and TeX 3965-3998.
Meanings, native interfaces, and endpoint checks precede these proofs in
-/

namespace DirichletL

open Filter
open scoped Classical

theorem exists_minimal_total_exponent {σ R : Type*} [CommRing R]
    (F : MvPowerSeries σ R) (hF : F ≠ 0) :
    ∃ n : σ →₀ ℕ, MvPowerSeries.coeff (R := R) n F ≠ 0 ∧
      ∀ e : σ →₀ ℕ, e.degree < n.degree → MvPowerSeries.coeff (R := R) e F = 0 := by
  obtain ⟨n, hn, horder⟩ := MvPowerSeries.exists_coeff_ne_zero_and_order
    (MvPowerSeries.ne_zero_iff_order_finite.mp hF)
  refine ⟨n, hn, ?_⟩
  intro e he
  apply MvPowerSeries.coeff_of_lt_order
  rw [← horder]
  exact_mod_cast he

theorem minimal_exponent_avoids_auxiliary_constraints {d L : ℕ} (R S ε : ℝ)
    (F : MvPowerSeries (Fin d) ℚ) (n : Fin d →₀ ℕ)
    (hn : MvPowerSeries.coeff (R := ℚ) n F ≠ 0) (hL : ∀ j, n j < L)
    (hzero : ∀ p : ↥(auxiliaryConstraintIndices d L R S ε),
      MvPowerSeries.coeff (R := ℚ) (Finsupp.equivFunOnFinite.symm (fun j => (p.val j).val)) F = 0) :
    HasIntervalDiscrepancyLE (fun j => (n j : ℝ) / R) ε ∧ ∃ j, S < (n j : ℝ) := by
  let p : Fin d → Fin L := fun j => ⟨n j, hL j⟩
  have he : Finsupp.equivFunOnFinite.symm (fun j => (p j).val) = n := by
    ext j
    rfl
  have hp : p ∉ auxiliaryConstraintIndices d L R S ε := by
    intro h
    apply hn
    simpa only [he] using hzero ⟨p, h⟩
  rw [mem_auxiliaryConstraintIndices, not_or, not_not] at hp
  refine ⟨hp.2, ?_⟩
  obtain ⟨j, hj⟩ := not_forall.mp hp.1
  exact ⟨j, lt_of_not_ge hj⟩

theorem exists_cdtAuxiliaryFormalSeries_controlled_minimum (a b c : ℤ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧ δ < 14 ∧ ∀ ζ : ℝ, 0 < ζ →
      ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop, ∀ L : ℕ,
        (14 + δ) * D ≤ L → (L : ℝ) ≤ (14 + δ) * D + 1 →
        ∃ (t : ↥(auxiliaryFreeIndices 14 h D ε) → ℤ) (n : Fin (14 * h) →₀ ℕ),
          t ≠ 0 ∧ (∀ p, |(t p : ℝ)| ≤ Real.exp (ζ * (14 * h : ℕ) * D)) ∧
          auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t ≠ 0 ∧
          MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) ≠ 0 ∧
          (∀ e : Fin (14 * h) →₀ ℕ, e.degree < n.degree →
            MvPowerSeries.coeff (R := ℚ) e (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) = 0) ∧
          (∀ j, n j < L) ∧
          HasIntervalDiscrepancyLE (fun j => (n j : ℝ) / ((14 + δ) * D)) ε ∧
          ∃ j, (14 - δ) * D < (n j : ℝ) := by
  obtain ⟨δ, hδ, hδε, hδm, hconstruction⟩ :=
    exists_cdtAuxiliaryFormalSeries_small_vanishing a b c hrel hne hε
  have hcube := eventually_minimal_exponent_lt_cdtAuxiliaryFormalSeries
    (a : ℚ) (b : ℚ) (c : ℚ) hδ
  refine ⟨δ, hδ, hδε, hδm, ?_⟩
  intro ζ hζ
  filter_upwards [hconstruction ζ hζ] with h hh
  filter_upwards [hh, hcube] with D hD hcubeD
  intro L hRL hLR
  obtain ⟨t, ht, hsize, hF, hzero⟩ := hD L hRL hLR
  obtain ⟨n, hn, hmin⟩ := exists_minimal_total_exponent
    (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) hF
  have hnL := hcubeD L hRL h ε t n hn hmin
  obtain ⟨hdiscrepancy, hlarge⟩ := minimal_exponent_avoids_auxiliary_constraints
    ((14 + δ) * D) ((14 - δ) * D) ε
    (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε t) n hn hnL hzero
  exact ⟨t, n, ht, hsize, hF, hn, hmin, hnL, hdiscrepancy, hlarge⟩

end DirichletL
