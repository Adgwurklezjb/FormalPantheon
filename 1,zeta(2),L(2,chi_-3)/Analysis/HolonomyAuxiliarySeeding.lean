import Analysis.HolonomyAuxiliaryCoefficientLowerBound
import Analysis.SeededVandermondeCoefficient

/-!
The actual small auxiliary series with one coefficient retained through all
formal seeding choices, CDT v2 TeX 3998-4028, 4100-4130, and 4304-4518.
The pre-proof meanings and quantifier checks are in
-/

namespace DirichletL

open Filter
open scoped Classical

theorem exists_cdtAuxiliaryFormalSeries_seeded_vandermonde_coefficient (a b c : ℤ)
    (hrel : (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) + (c : ℝ) * (zetaTwo / 4) = 0)
    (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0)) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ ε' δ : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ ε' ≤ 1 ∧ 0 < δ ∧ δ < ε' ∧ δ < 14 ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ h : ℕ in atTop, ∀ᶠ D : ℕ in atTop, ∀ L : ℕ,
        (14 + δ) * D ≤ L → (L : ℝ) ≤ (14 + δ) * D + 1 →
        ∃ (t : ↥(auxiliaryFreeIndices 14 h D ε') → ℤ)
          (n : Fin (14 * h) →₀ ℕ) (σ : Equiv.Perm (Fin (14 * h))),
          let F := auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε' t
          let p := Finsupp.equivFunOnFinite.symm (fun j => n (σ j))
          let A := MvPowerSeries.map (σ := (Fin (14 * h))) (algebraMap ℚ ℂ)
            (MvPowerSeries.subst (fun i => (MvPowerSeries.X (σ.symm i) :
              MvPowerSeries (Fin (14 * h)) ℚ)) F)
          t ≠ 0 ∧ (∀ v, |(t v : ℝ)| ≤ Real.exp (ζ * (14 * h : ℕ) * D)) ∧ F ≠ 0 ∧
            MvPowerSeries.coeff (R := ℚ) n F ≠ 0 ∧
            (∀ e : Fin (14 * h) →₀ ℕ, e.degree < n.degree → MvPowerSeries.coeff (R := ℚ) e F = 0) ∧
            Monotone (fun j => n (σ j)) ∧ (∀ j, n j < L) ∧
            HasIntervalDiscrepancyLE (fun j => (n j : ℝ) / ((14 + δ) * D)) ε' ∧
            (∃ j, (14 - δ) * D < (n j : ℝ)) ∧
            -Real.log |(MvPowerSeries.coeff (R := ℚ) n F : ℝ)| ≤
              98 * (h : ℝ) * D * ((16603 / 3920 : ℝ) + η) ∧
            ∀ (H : MvPowerSeries (Fin (14 * h)) ℂ) (φ : Fin (14 * h) → PowerSeries ℂ),
              MvPowerSeries.constantCoeff (σ := (Fin (14 * h))) (R := ℂ) H = 1 →
              (∀ j, PowerSeries.constantCoeff (R := ℂ) (φ j) = 0) →
              (∀ j, PowerSeries.coeff (R := ℂ) 1 (φ j) ≠ 0) →
              ∀ P : Finset (Fin (14 * h) × Fin (14 * h)),
                (∀ ij ∈ P, ij.1 < ij.2) → ∀ M : ℕ,
                let q := ∑ ij ∈ P, M • Finsupp.single ij.2 (1 : ℕ)
                let G := H * MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ j)) A
                let W := ∏ ij ∈ P, (MvPowerSeries.X ij.2 - MvPowerSeries.X ij.1 :
                  MvPowerSeries (Fin (14 * h)) ℂ) ^ M
                MvPowerSeries.coeff (R := ℂ) (p + q) (W * G) =
                    (MvPowerSeries.coeff (R := ℚ) n F : ℂ) *
                      ∏ j, PowerSeries.coeff (R := ℂ) 1 (φ j) ^ p j ∧
                  MvPowerSeries.coeff (R := ℂ) (p + q) (W * G) ≠ 0 := by
  obtain ⟨ε', δ, hε', hε'ε, hε'1, hδ, hδε', hδ14, hc⟩ :=
    exists_cdtAuxiliaryFormalSeries_minimum_coefficient_lower_bound a b c hrel hne hε hη
  refine ⟨ε', δ, hε', hε'ε, hε'1, hδ, hδε', hδ14, ?_⟩
  intro ζ hζ
  filter_upwards [hc ζ hζ] with h hch
  filter_upwards [hch] with D hcD
  intro L hRL hLR
  obtain ⟨t, ht, hsize, hF, hcoeff⟩ := hcD L hRL hLR
  obtain ⟨n, σ, hn, hmin, hmono, hseed⟩ := exists_sorted_seeded_vandermonde_coefficient
    (auxiliaryFormalSeries (cdtHolonomySeries a b c) h D ε' t) hF
  obtain ⟨hnL, hdis, hlarge, hbound⟩ := hcoeff n hn hmin
  exact ⟨t, n, σ, ht, hsize, hF, hn, hmin, hmono, hnL, hdis, hlarge, hbound, hseed⟩

end DirichletL
