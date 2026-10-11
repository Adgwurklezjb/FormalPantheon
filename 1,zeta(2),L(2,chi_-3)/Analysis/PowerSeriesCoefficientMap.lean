import Analysis.PowerSeriesPermutation

/-!
Injective coefficient transfer in the seeding argument of CDT v2, supplied
TeX 3998-4028. Its meaning precedes this proof in
-/

namespace DirichletL

theorem minimum_coefficient_map {d : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (F : MvPowerSeries (Fin d) R)
    (p : Fin d →₀ ℕ) (hp : MvPowerSeries.coeff (R := R) p F ≠ 0)
    (hF : ∀ e : Fin d →₀ ℕ, e.degree < p.degree → MvPowerSeries.coeff (R := R) e F = 0)
    (hle : ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) e F ≠ 0 → e.degree = p.degree →
      toLex p ≤ toLex e) :
    MvPowerSeries.coeff (R := S) p (MvPowerSeries.map (σ := (Fin d)) f F) = f (MvPowerSeries.coeff (R := R) p F) ∧
      MvPowerSeries.coeff (R := S) p (MvPowerSeries.map (σ := (Fin d)) f F) ≠ 0 ∧
      (∀ e : Fin d →₀ ℕ, e.degree < p.degree →
        MvPowerSeries.coeff (R := S) e (MvPowerSeries.map (σ := (Fin d)) f F) = 0) ∧
      ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := S) e (MvPowerSeries.map (σ := (Fin d)) f F) ≠ 0 →
        e.degree = p.degree → toLex p ≤ toLex e := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa only [MvPowerSeries.coeff_map, map_ne_zero_iff f hf] using hp
  · intro e he
    simp only [MvPowerSeries.coeff_map, hF e he, map_zero]
  · intro e he hdeg
    apply hle e ?_ hdeg
    simpa only [MvPowerSeries.coeff_map, map_ne_zero_iff f hf] using he

end DirichletL
