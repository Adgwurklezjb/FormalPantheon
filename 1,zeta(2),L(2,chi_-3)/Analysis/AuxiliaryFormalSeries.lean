import Analysis.AuxiliaryParameterIndices
import Analysis.MultivariateSeriesIndependence

/-!
The literal auxiliary series and coefficient formula in CDT v2,
supplied TeX 3965-3998. Nonvanishing uses the full monomial family
before restricting to the actual finite free indices.
-/

noncomputable section

namespace DirichletL

open scoped Classical

/-- One monomial shift of a product of series in separate variables. -/
def auxiliarySeriesTerm {R : Type*} [CommRing R] {m d D : ℕ}
    (f : Fin m → PowerSeries R) (p : (Fin d → Fin m) × (Fin d → Fin D)) :
    MvPowerSeries (Fin d) R :=
  MvPowerSeries.monomial (R := R) (Finsupp.equivFunOnFinite.symm (fun j => (p.2 j).val)) 1 *
    ∏ j, powerSeriesInVariable R j (f (p.1 j))

theorem coeff_auxiliarySeriesTerm {R : Type*} [CommRing R] {m d D : ℕ}
    (f : Fin m → PowerSeries R) (p : (Fin d → Fin m) × (Fin d → Fin D))
    (n : Fin d →₀ ℕ) :
    MvPowerSeries.coeff (R := R) n (auxiliarySeriesTerm f p) =
      if ∀ j, (p.2 j).val ≤ n j then
        ∏ j, PowerSeries.coeff (R := R) (n j - (p.2 j).val) (f (p.1 j)) else 0 := by
  simp [auxiliarySeriesTerm, MvPowerSeries.coeff_monomial_mul,
    coeff_prod_powerSeriesInVariable, Finsupp.le_def]

/-- The integer coefficient vector evaluated in the actual rational series template. -/
def auxiliaryFormalSeries {m : ℕ} (f : Fin m → PowerSeries ℚ) (h D : ℕ) (ε : ℝ)
    (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) : MvPowerSeries (Fin (m * h)) ℚ :=
  ∑ p, (t p : ℚ) • auxiliarySeriesTerm f p.val

theorem coeff_auxiliaryFormalSeries {m : ℕ} (f : Fin m → PowerSeries ℚ) (h D : ℕ) (ε : ℝ)
    (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) (n : Fin (m * h) →₀ ℕ) :
    MvPowerSeries.coeff (R := ℚ) n (auxiliaryFormalSeries f h D ε t) =
      ∑ p : ↥(auxiliaryFreeIndices m h D ε), (t p : ℚ) *
        (if ∀ j, (p.val.2 j).val ≤ n j then
          ∏ j, PowerSeries.coeff (R := ℚ) (n j - (p.val.2 j).val) (f (p.val.1 j)) else 0) := by
  simp only [auxiliaryFormalSeries, map_sum, map_smul, smul_eq_mul, coeff_auxiliarySeriesTerm]

theorem linearIndependent_auxiliarySeriesTerm {K : Type*} [Field K] {m : ℕ}
    (f : Fin m → PowerSeries K)
    (hf : ∀ P : Fin m → Polynomial K, ∑ i, (P i : PowerSeries K) * f i = 0 → P = 0)
    (h D : ℕ) (ε : ℝ) :
    LinearIndependent K (fun p : ↥(auxiliaryFreeIndices m h D ε) => auxiliarySeriesTerm f p.val) :=
  (linearIndependent_shifted_prod_powerSeries f hf (m * h) D).comp
    Subtype.val Subtype.val_injective

theorem auxiliaryFormalSeries_ne_zero {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (hf : ∀ P : Fin m → Polynomial ℚ, ∑ i, (P i : PowerSeries ℚ) * f i = 0 → P = 0)
    (h D : ℕ) (ε : ℝ) (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) (ht : t ≠ 0) :
    auxiliaryFormalSeries f h D ε t ≠ 0 := by
  intro hz
  apply ht
  funext p
  have hp := Fintype.linearIndependent_iff.mp (linearIndependent_auxiliarySeriesTerm f hf h D ε)
    (fun p => (t p : ℚ)) (by simpa only [auxiliaryFormalSeries] using hz) p
  exact_mod_cast hp

end DirichletL
