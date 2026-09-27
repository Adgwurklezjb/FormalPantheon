import Analysis.PowerSeriesCoordinates
import Arithmetic.PowerSeriesInverse

/-!
Formal separate-coordinate substitution for CDT v2's `G coeff`, supplied
TeX 3998-4028. Meanings and edge cases precede these bodies in
-/

namespace DirichletL

open scoped Classical

theorem coeff_subst_powerSeriesInVariable {σ R : Type*} [Fintype σ] [CommRing R]
    (F : MvPowerSeries σ R) (φ : σ → PowerSeries R)
    (hφ : ∀ j, PowerSeries.constantCoeff (R := R) (φ j) = 0) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff (R := R) n
        (MvPowerSeries.subst (fun j => powerSeriesInVariable R j (φ j)) F) =
      ∑ᶠ e : σ →₀ ℕ, MvPowerSeries.coeff (R := R) e F *
        ∏ j, PowerSeries.coeff (R := R) (n j) (φ j ^ e j) := by
  have ha : MvPowerSeries.HasSubst (fun j => powerSeriesInVariable R j (φ j)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_powerSeriesInVariable]
    simpa only [Finsupp.zero_apply, Finsupp.single_zero, ite_true,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] using hφ j
  have hprod (e : σ →₀ ℕ) :
      e.prod (fun j k => powerSeriesInVariable R j (φ j) ^ k) =
        ∏ j, powerSeriesInVariable R j (φ j ^ e j) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    exact Finset.prod_congr rfl (fun j _ =>
      (map_pow (powerSeriesInVariable R j) (φ j) (e j)).symm)
  rw [MvPowerSeries.coeff_subst ha]
  apply finsum_congr
  intro e
  rw [hprod, coeff_prod_powerSeriesInVariable, smul_eq_mul]

theorem coeff_subst_separate_of_degree_le {σ R : Type*} [Fintype σ] [CommRing R]
    (F : MvPowerSeries σ R) (φ : σ → PowerSeries R)
    (hφ : ∀ j, PowerSeries.constantCoeff (R := R) (φ j) = 0) (N : ℕ)
    (hF : ∀ e : σ →₀ ℕ, e.degree < N → MvPowerSeries.coeff (R := R) e F = 0)
    (n : σ →₀ ℕ) (hn : n.degree ≤ N) :
    MvPowerSeries.coeff (R := R) n
        (MvPowerSeries.subst (fun j => powerSeriesInVariable R j (φ j)) F) =
      MvPowerSeries.coeff (R := R) n F * ∏ j, PowerSeries.coeff (R := R) 1 (φ j) ^ n j := by
  rw [coeff_subst_powerSeriesInVariable F φ hφ n, finsum_eq_single _ n]
  · congr 1
    exact Finset.prod_congr rfl (fun j _ =>
      coeff_pow_self_of_constantCoeff_zero (φ j) (hφ j) (n j))
  · intro e he
    by_cases hle : ∀ j, e j ≤ n j
    · have hstrict : ∃ j, e j < n j := by
        by_contra h
        apply he
        ext j
        exact le_antisymm (hle j) (le_of_not_gt (fun hj => h ⟨j, hj⟩))
      have hdeg (p : σ →₀ ℕ) : p.degree = ∑ j, p j :=
        Finsupp.sum_fintype p (fun _ k => k) (fun _ => rfl)
      have hedeg : e.degree < n.degree := by
        rw [hdeg e, hdeg n]
        obtain ⟨j, hj⟩ := hstrict
        exact Finset.sum_lt_sum (fun i _ => hle i) ⟨j, Finset.mem_univ j, hj⟩
      rw [hF e (hedeg.trans_le hn), zero_mul]
    · obtain ⟨j, hj⟩ := not_forall.mp hle
      have hz : PowerSeries.coeff (R := R) (n j) (φ j ^ e j) = 0 :=
        PowerSeries.X_pow_dvd_iff.mp
          (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr (hφ j)) (e j))
          (n j) (lt_of_not_ge hj)
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero]

end DirichletL
