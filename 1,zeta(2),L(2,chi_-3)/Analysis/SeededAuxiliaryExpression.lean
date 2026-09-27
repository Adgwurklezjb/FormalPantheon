import Analysis.SeparateSubstitutionAlgebra
import Analysis.AuxiliaryFormalSeries

/-!
The literal seeded expression in CDT v2, supplied TeX 3965-3998 and 4008-4028.
Its index and permutation meanings precede these proofs in
-/

namespace DirichletL

open scoped Classical

theorem auxiliarySeriesTerm_eq_prod {R : Type*} [CommRing R] {m d D : ℕ}
    (f : Fin m → PowerSeries R) (v : (Fin d → Fin m) × (Fin d → Fin D)) :
    auxiliarySeriesTerm f v =
      ∏ j, powerSeriesInVariable R j (PowerSeries.X ^ (v.2 j).val * f (v.1 j)) := by
  simpa only [auxiliarySeriesTerm, PowerSeries.X_pow_eq] using
    (prod_powerSeriesInVariable_shift (fun j => f (v.1 j)) (fun j => (v.2 j).val)).symm

theorem auxiliaryFormalSeries_eq_sum_separate {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (h D : ℕ) (ε : ℝ) (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ) :
    auxiliaryFormalSeries f h D ε t =
      ∑ v, MvPowerSeries.C (σ := (Fin (m * h))) (R := ℚ) (t v : ℚ) *
        ∏ j, powerSeriesInVariable ℚ j (PowerSeries.X ^ (v.val.2 j).val * f (v.val.1 j)) := by
  simp only [auxiliaryFormalSeries, MvPowerSeries.smul_eq_C_mul, auxiliarySeriesTerm_eq_prod]

theorem seeded_auxiliaryFormalSeries_eq_sum {m : ℕ} (f : Fin m → PowerSeries ℚ)
    (h D : ℕ) (ε : ℝ) (t : ↥(auxiliaryFreeIndices m h D ε) → ℤ)
    (π : Equiv.Perm (Fin (m * h))) (φ : Fin (m * h) → PowerSeries ℂ) (H : PowerSeries ℂ)
    (hφ : ∀ j, PowerSeries.constantCoeff (R := ℂ) (φ j) = 0) :
    (∏ j, powerSeriesInVariable ℂ j H) *
      MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ j))
        (MvPowerSeries.map (σ := (Fin (m * h))) (algebraMap ℚ ℂ)
          (MvPowerSeries.subst
            (fun j => (MvPowerSeries.X (π.symm j) : MvPowerSeries (Fin (m * h)) ℚ))
            (auxiliaryFormalSeries f h D ε t))) =
      ∑ v, MvPowerSeries.C (σ := (Fin (m * h))) (R := ℂ) (t v : ℂ) *
        ∏ j, powerSeriesInVariable ℂ j
          (H * (φ j ^ (v.val.2 (π j)).val * MvPowerSeries.subst (fun _ : Unit => φ j)
            (PowerSeries.map (algebraMap ℚ ℂ) (f (v.val.1 (π j)))))) := by
  rw [auxiliaryFormalSeries_eq_sum_separate,
    seeded_separate_sum_eq (algebraMap ℚ ℂ) _ _ π φ (fun _ => H) hφ]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_intCast]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  have hφj : MvPowerSeries.HasSubst (fun _ : Unit => φ j) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hφ j)
  simp only [map_mul, map_pow, PowerSeries.map_X]
  rw [MvPowerSeries.subst_mul hφj, MvPowerSeries.subst_pow hφj]
  simp only [PowerSeries.X, MvPowerSeries.subst_X hφj]

end DirichletL
