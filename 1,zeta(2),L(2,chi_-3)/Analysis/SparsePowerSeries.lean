import Analysis.FormalSeriesAlgebra
import Analysis.PowerSeriesEvaluation

/-!
Sparse coefficients and convergent evaluation for the theta series in
CDT v2 Section 11.1. Exponent embeddings use Mathlib's extension by zero;
formal coefficientwise summation and complex evaluation are kept explicit.
-/

namespace DirichletL

variable {R : Type*} [CommRing R]

/-- The series with coefficient `c i` at degree `e i`, and zero elsewhere. -/
noncomputable def sparsePowerSeries (e : ℕ ↪ ℕ) (c : ℕ → R) : PowerSeries R :=
  PowerSeries.mk (Function.extend e c 0)

@[simp] theorem coeff_sparsePowerSeries_apply (e : ℕ ↪ ℕ) (c : ℕ → R) (i : ℕ) :
    PowerSeries.coeff (R := R) (e i) (sparsePowerSeries e c) = c i := by
  simp only [sparsePowerSeries, PowerSeries.coeff_mk, e.injective.extend_apply]

theorem coeff_sparsePowerSeries_eq_zero (e : ℕ ↪ ℕ) (c : ℕ → R) {n : ℕ}
    (hn : n ∉ Set.range e) : PowerSeries.coeff (R := R) n (sparsePowerSeries e c) = 0 := by
  simp only [sparsePowerSeries, PowerSeries.coeff_mk]
  exact Function.extend_apply' c (0 : ℕ → R) n hn

theorem map_sparsePowerSeries {S : Type*} [CommRing S] (φ : R →+* S)
    (e : ℕ ↪ ℕ) (c : ℕ → R) :
    PowerSeries.map φ (sparsePowerSeries e c) = sparsePowerSeries e (fun i => φ (c i)) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map]
  by_cases hn : n ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hn
    simp
  · rw [coeff_sparsePowerSeries_eq_zero e c hn,
      coeff_sparsePowerSeries_eq_zero e (fun i => φ (c i)) hn, map_zero]

open scoped PowerSeries.WithPiTopology

theorem hasSum_sparsePowerSeries [TopologicalSpace R] (e : ℕ ↪ ℕ) (c : ℕ → R) :
    HasSum (fun i => PowerSeries.C (R := R) (c i) * PowerSeries.X ^ e i) (sparsePowerSeries e c) := by
  classical
  rw [hasSum_powerSeries_iff_coeff]
  intro n
  by_cases hn : n ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hn
    rw [coeff_sparsePowerSeries_apply]
    convert hasSum_ite_eq i (c i) using 1
    ext j
    by_cases hj : j = i
    · subst j
      simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    · have he : e i ≠ e j := fun h => hj (e.injective h).symm
      simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, hj, he]
  · rw [coeff_sparsePowerSeries_eq_zero e c hn]
    have hzero (i : ℕ) : PowerSeries.coeff (R := R) n (PowerSeries.C (R := R) (c i) *
        PowerSeries.X ^ e i) = 0 := by
      have he : n ≠ e i := fun h => hn ⟨i, h.symm⟩
      simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, he]
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : R)) 0)

theorem hasSum_sparsePowerSeries_eval (e : ℕ ↪ ℕ) (c : ℕ → ℚ) {z a : ℂ}
    (h : HasSum (fun i => (c i : ℂ) * z ^ e i) a) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (sparsePowerSeries e c) : ℂ) * z ^ n) a := by
  apply (e.injective.hasSum_iff ?_).mp
  · simpa only [Function.comp_def, coeff_sparsePowerSeries_apply] using h
  · intro n hn
    rw [coeff_sparsePowerSeries_eq_zero e c hn, Rat.cast_zero, zero_mul]

theorem sum_complexSeries_sparsePowerSeries (e : ℕ ↪ ℕ) (c : ℕ → ℚ) {z a : ℂ}
    (h : HasSum (fun i => (c i : ℂ) * z ^ e i) a) :
    (complexSeries (sparsePowerSeries e c)).sum z = a :=
  sum_complexSeries_eq_of_hasSum (hasSum_sparsePowerSeries_eval e c h)

end DirichletL
