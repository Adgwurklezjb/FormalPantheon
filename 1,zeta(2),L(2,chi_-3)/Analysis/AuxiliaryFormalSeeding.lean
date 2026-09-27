import Analysis.PowerSeriesCoordinateSubstitution
import Analysis.HomogeneousSeriesProduct

/-!
Formal seeding and preservation of the extreme minimum coefficient for
CDT v2, supplied TeX 3998-4028, and published UDC Section 2.5.25, page 648.
-/

namespace DirichletL

open scoped Classical

theorem coeff_seeded_series_of_degree_le {σ R : Type*} [Fintype σ] [CommRing R]
    (F H : MvPowerSeries σ R) (φ : σ → PowerSeries R)
    (hφ : ∀ j, PowerSeries.constantCoeff (R := R) (φ j) = 0) (N : ℕ)
    (hF : ∀ e : σ →₀ ℕ, e.degree < N → MvPowerSeries.coeff (R := R) e F = 0)
    (n : σ →₀ ℕ) (hn : n.degree ≤ N) :
    MvPowerSeries.coeff (R := R) n
        (H * MvPowerSeries.subst (fun j => powerSeriesInVariable R j (φ j)) F) =
      MvPowerSeries.constantCoeff (σ := σ) (R := R) H * MvPowerSeries.coeff (R := R) n F *
        ∏ j, PowerSeries.coeff (R := R) 1 (φ j) ^ n j := by
  have hB : ∀ e : σ →₀ ℕ, e.degree < n.degree →
      MvPowerSeries.coeff (R := R) e
        (MvPowerSeries.subst (fun j => powerSeriesInVariable R j (φ j)) F) = 0 := by
    intro e he
    rw [coeff_subst_separate_of_degree_le F φ hφ N hF e (he.le.trans hn),
      hF e (he.trans_le hn), zero_mul]
  rw [coeff_mul_of_minimal_total H _ n hB,
    coeff_subst_separate_of_degree_le F φ hφ N hF n hn, mul_assoc]

theorem minimum_coefficient_seeded_series {d : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (F H : MvPowerSeries (Fin d) R) (φ : Fin d → PowerSeries R)
    (hφ : ∀ j, PowerSeries.constantCoeff (R := R) (φ j) = 0)
    (hlinear : ∀ j, PowerSeries.coeff (R := R) 1 (φ j) ≠ 0)
    (hH : MvPowerSeries.constantCoeff (σ := (Fin d)) (R := R) H = 1) (p : Fin d →₀ ℕ)
    (hp : MvPowerSeries.coeff (R := R) p F ≠ 0)
    (hF : ∀ e : Fin d →₀ ℕ, e.degree < p.degree → MvPowerSeries.coeff (R := R) e F = 0)
    (hle : ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) e F ≠ 0 → e.degree = p.degree →
      toLex p ≤ toLex e) :
    let G := H * MvPowerSeries.subst (fun j => powerSeriesInVariable R j (φ j)) F
    MvPowerSeries.coeff (R := R) p G =
        MvPowerSeries.coeff (R := R) p F * ∏ j, PowerSeries.coeff (R := R) 1 (φ j) ^ p j ∧
      MvPowerSeries.coeff (R := R) p G ≠ 0 ∧
      (∀ e : Fin d →₀ ℕ, e.degree < p.degree → MvPowerSeries.coeff (R := R) e G = 0) ∧
      ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) e G ≠ 0 → e.degree = p.degree →
        toLex p ≤ toLex e := by
  have hcoeff (e : Fin d →₀ ℕ) (he : e.degree ≤ p.degree) :
      MvPowerSeries.coeff (R := R) e
          (H * MvPowerSeries.subst (fun j => powerSeriesInVariable R j (φ j)) F) =
        MvPowerSeries.coeff (R := R) e F * ∏ j, PowerSeries.coeff (R := R) 1 (φ j) ^ e j := by
    simpa only [hH, one_mul] using
      coeff_seeded_series_of_degree_le F H φ hφ p.degree hF e he
  refine ⟨hcoeff p le_rfl, ?_, ?_, ?_⟩
  · rw [hcoeff p le_rfl]
    exact mul_ne_zero hp (Finset.prod_ne_zero_iff.mpr (fun j _ =>
      pow_ne_zero (p j) (hlinear j)))
  · intro e he
    rw [hcoeff e he.le, hF e he, zero_mul]
  · intro e he hdeg
    apply hle e ?_ hdeg
    intro heF
    apply he
    rw [hcoeff e hdeg.le, heF, zero_mul]

end DirichletL
