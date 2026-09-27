import Analysis.AuxiliaryFormalSeeding
import Analysis.PowerSeriesCoefficientMap
import Analysis.VandermondeCoefficient

/-!
The rational coefficient through complex formal seeding and Vandermonde
multiplication, CDT v2 TeX 3998-4028 and 4100-4130. The corrected shift,
nonzero factors, and quantifier order are recorded before these proofs in
-/

namespace DirichletL

open scoped Classical

theorem exists_sorted_seeded_vandermonde_coefficient {d : ℕ}
    (F : MvPowerSeries (Fin d) ℚ) (hF : F ≠ 0) :
    ∃ (n : Fin d →₀ ℕ) (σ : Equiv.Perm (Fin d)),
      MvPowerSeries.coeff (R := ℚ) n F ≠ 0 ∧
      (∀ e : Fin d →₀ ℕ, e.degree < n.degree → MvPowerSeries.coeff (R := ℚ) e F = 0) ∧
      Monotone (fun j => n (σ j)) ∧
      let p := Finsupp.equivFunOnFinite.symm (fun j => n (σ j))
      let A := MvPowerSeries.map (σ := (Fin d)) (algebraMap ℚ ℂ)
        (MvPowerSeries.subst (fun i => (MvPowerSeries.X (σ.symm i) :
          MvPowerSeries (Fin d) ℚ)) F)
      ∀ (H : MvPowerSeries (Fin d) ℂ) (φ : Fin d → PowerSeries ℂ),
        MvPowerSeries.constantCoeff (σ := (Fin d)) (R := ℂ) H = 1 →
        (∀ j, PowerSeries.constantCoeff (R := ℂ) (φ j) = 0) →
        (∀ j, PowerSeries.coeff (R := ℂ) 1 (φ j) ≠ 0) →
        ∀ P : Finset (Fin d × Fin d), (∀ ij ∈ P, ij.1 < ij.2) → ∀ M : ℕ,
          let q := ∑ ij ∈ P, M • Finsupp.single ij.2 (1 : ℕ)
          let G := H * MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ j)) A
          let W := ∏ ij ∈ P, (MvPowerSeries.X ij.2 - MvPowerSeries.X ij.1 :
            MvPowerSeries (Fin d) ℂ) ^ M
          MvPowerSeries.coeff (R := ℂ) (p + q) (W * G) =
              (MvPowerSeries.coeff (R := ℚ) n F : ℂ) * ∏ j, PowerSeries.coeff (R := ℂ) 1 (φ j) ^ p j ∧
            MvPowerSeries.coeff (R := ℂ) (p + q) (W * G) ≠ 0 := by
  obtain ⟨n, σ, hn, hmin, hmono, hc, hlow, hleast⟩ :=
    exists_minimum_coefficient_subst_perm_monotone F hF
  let p := Finsupp.equivFunOnFinite.symm (fun j => n (σ j))
  let Fσ := MvPowerSeries.subst (fun i => (MvPowerSeries.X (σ.symm i) :
    MvPowerSeries (Fin d) ℚ)) F
  let A := MvPowerSeries.map (σ := (Fin d)) (algebraMap ℚ ℂ) Fσ
  have hp : MvPowerSeries.coeff (R := ℚ) p Fσ ≠ 0 := hc.trans_ne hn
  obtain ⟨hmap, hpA, hlowA, hleastA⟩ := minimum_coefficient_map
    (algebraMap ℚ ℂ) (by exact Rat.cast_injective) Fσ p hp hlow hleast
  have hbeta : MvPowerSeries.coeff (R := ℂ) p A = (MvPowerSeries.coeff (R := ℚ) n F : ℂ) :=
    hmap.trans (congrArg (algebraMap ℚ ℂ) hc)
  refine ⟨n, σ, hn, hmin, hmono, ?_⟩
  dsimp only
  intro H φ hH hφ hlinear P hP M
  obtain ⟨hseed, hseed0, hseedlow, hseedleast⟩ :=
    minimum_coefficient_seeded_series A H φ hφ hlinear hH p hpA hlowA hleastA
  have hw := coeff_vandermondeProduct_mul_of_min_total_lex P hP M
    (H * MvPowerSeries.subst (fun j => powerSeriesInVariable ℂ j (φ j)) A)
    p hseed0 hseedlow hseedleast
  refine ⟨?_, hw.trans_ne hseed0⟩
  simpa only [hbeta] using hw.trans hseed

theorem log_norm_rat_mul_prod_pow {ι : Type*} [Fintype ι]
    (β : ℚ) (hβ : β ≠ 0) (u : ι → ℂ) (hu : ∀ j, u j ≠ 0) (p : ι → ℕ) :
    Real.log ‖(β : ℂ) * ∏ j, u j ^ p j‖ =
      Real.log |(β : ℝ)| + ∑ j, (p j : ℝ) * Real.log ‖u j‖ := by
  have hβR : (β : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr hβ
  have hp (j : ι) : ‖u j ^ p j‖ ≠ 0 := norm_ne_zero_iff.mpr (pow_ne_zero _ (hu j))
  rw [norm_mul, norm_prod, Complex.norm_ratCast,
    Real.log_mul (abs_ne_zero.mpr hβR) (Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)),
    Real.log_prod Finset.univ _ (fun j _ => hp j)]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by rw [norm_pow, Real.log_pow])

theorem sum_log_norm_le_of_coeff_bounds {ι : Type*} [Fintype ι]
    (β : ℚ) (hβ : β ≠ 0) (u : ι → ℂ) (hu : ∀ j, u j ≠ 0) (p : ι → ℕ)
    (γ : ℂ) (hγ : γ = (β : ℂ) * ∏ j, u j ^ p j) (A B : ℝ)
    (hlower : -Real.log |(β : ℝ)| ≤ A) (hupper : ‖γ‖ ≤ Real.exp B) :
    (∑ j, (p j : ℝ) * Real.log ‖u j‖) ≤ A + B := by
  have hγ0 : γ ≠ 0 := by
    rw [hγ]
    exact mul_ne_zero (Rat.cast_ne_zero.mpr hβ)
      (Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero _ (hu j)))
  have hlog := Real.log_le_log (norm_pos_iff.mpr hγ0) hupper
  rw [Real.log_exp, hγ, log_norm_rat_mul_prod_pow β hβ u hu p] at hlog
  linarith

end DirichletL
