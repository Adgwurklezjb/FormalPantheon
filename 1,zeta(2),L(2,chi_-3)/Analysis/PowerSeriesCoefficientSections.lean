import Analysis.PowerSeriesCoordinates

/-!
Coefficient sections for CDT v2, supplied TeX 2910-2935, and the
separated auxiliary products at TeX 3965-3998.
-/

noncomputable section

namespace DirichletL

open scoped Classical

/-- Fix all exponents except one and retain that coordinate as a power series. -/
def powerSeriesCoefficientSection {σ : Type*} (R : Type*) [CommRing R]
    (j : σ) (n : σ →₀ ℕ) : MvPowerSeries σ R →ₗ[R] PowerSeries R where
  toFun F := PowerSeries.mk (fun k => MvPowerSeries.coeff (R := R) (n.update j k) F)
  map_add' F G := by
    ext k
    simp only [PowerSeries.coeff_mk, map_add]
  map_smul' c F := by
    ext k
    simp only [PowerSeries.coeff_mk, map_smul, RingHom.id_apply]

@[simp]
theorem coeff_powerSeriesCoefficientSection {σ R : Type*} [CommRing R]
    (j : σ) (n : σ →₀ ℕ) (F : MvPowerSeries σ R) (k : ℕ) :
    PowerSeries.coeff (R := R) k (powerSeriesCoefficientSection R j n F) =
      MvPowerSeries.coeff (R := R) (n.update j k) F := by
  simp only [powerSeriesCoefficientSection, LinearMap.coe_mk, AddHom.coe_mk,
    PowerSeries.coeff_mk]

theorem powerSeriesCoefficientSection_prod {σ R : Type*} [Fintype σ] [CommRing R]
    (j : σ) (n : σ →₀ ℕ) (f : σ → PowerSeries R) :
    powerSeriesCoefficientSection R j n (∏ l, powerSeriesInVariable R l (f l)) =
      (∏ l ∈ Finset.univ.erase j, PowerSeries.coeff (R := R) (n l) (f l)) • f j := by
  ext k
  rw [coeff_powerSeriesCoefficientSection, coeff_prod_powerSeriesInVariable,
    map_smul, smul_eq_mul]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun l => PowerSeries.coeff (R := R) ((n.update j k) l) (f l)) (Finset.mem_univ j)]
  simp only [Finsupp.coe_update, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  simp only [Function.update_of_ne (Finset.mem_erase.mp hl).1]

theorem finsupp_degree_update_lt {σ : Type*} (n : σ →₀ ℕ) (j : σ) (k : ℕ)
    (hk : k < n j) : (n.update j k).degree < n.degree := by
  have h := Finsupp.sum_update_add n j k (fun _ a => a)
    (fun _ => rfl) (fun _ _ _ => rfl)
  change (n.update j k).degree + n j = n.degree + k at h
  omega

theorem order_powerSeriesCoefficientSection_of_minimal {σ R : Type*} [CommRing R]
    (F : MvPowerSeries σ R) (n : σ →₀ ℕ) (j : σ)
    (hn : MvPowerSeries.coeff (R := R) n F ≠ 0)
    (hmin : ∀ e : σ →₀ ℕ, e.degree < n.degree → MvPowerSeries.coeff (R := R) e F = 0) :
    (powerSeriesCoefficientSection R j n F).order = n j := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · simpa only [coeff_powerSeriesCoefficientSection, Finsupp.update_self] using hn
  · intro k hk
    rw [coeff_powerSeriesCoefficientSection]
    exact hmin _ (finsupp_degree_update_lt n j k hk)

theorem minimal_exponent_lt_of_separated_series_order_bound {σ ι R : Type*}
    [Fintype σ] [Fintype ι] [CommRing R]
    (f : ι → σ → PowerSeries R) (t : ι → R) (V : σ → Submodule R (PowerSeries R))
    (hf : ∀ p j, f p j ∈ V j) (N : σ → ℕ)
    (hbound : ∀ j u, u ∈ V j → u ≠ 0 → u.order < N j)
    (n : σ →₀ ℕ)
    (hn : MvPowerSeries.coeff (R := R) n (∑ p, t p • ∏ j, powerSeriesInVariable R j (f p j)) ≠ 0)
    (hmin : ∀ e : σ →₀ ℕ, e.degree < n.degree →
      MvPowerSeries.coeff (R := R) e (∑ p, t p • ∏ j, powerSeriesInVariable R j (f p j)) = 0) :
    ∀ j, n j < N j := by
  let F : MvPowerSeries σ R := ∑ p, t p • ∏ j, powerSeriesInVariable R j (f p j)
  intro j
  have hmem : powerSeriesCoefficientSection R j n F ∈ V j := by
    change powerSeriesCoefficientSection R j n
      (∑ p, t p • ∏ l, powerSeriesInVariable R l (f p l)) ∈ V j
    rw [map_sum]
    apply Submodule.sum_mem
    intro p _
    rw [map_smul, powerSeriesCoefficientSection_prod]
    exact (V j).smul_mem _ ((V j).smul_mem _ (hf p j))
  have hne : powerSeriesCoefficientSection R j n F ≠ 0 := by
    intro hz
    have hc := congrArg (PowerSeries.coeff (R := R) (n j)) hz
    simp only [coeff_powerSeriesCoefficientSection, Finsupp.update_self, map_zero] at hc
    exact hn hc
  have hb := hbound j _ hmem hne
  rw [order_powerSeriesCoefficientSection_of_minimal F n j hn hmin] at hb
  exact ENat.coe_lt_coe.mp hb

end DirichletL
