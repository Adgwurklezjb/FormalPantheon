import Analysis.PowerSeriesCoordinates

/-!
Separate-variable algebra in CDT v2, supplied TeX 3965-3998 and 3998-4028.
The coefficient-map and inverse-permutation meanings precede these proofs
-/

namespace DirichletL

open scoped Classical

theorem map_powerSeriesInVariable {σ R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (j : σ) (p : PowerSeries R) :
    MvPowerSeries.map (σ := σ) g (powerSeriesInVariable R j p) =
      powerSeriesInVariable S j (PowerSeries.map g p) := by
  ext n
  rw [MvPowerSeries.coeff_map, coeff_powerSeriesInVariable,
    coeff_powerSeriesInVariable, PowerSeries.coeff_map]
  split_ifs <;> simp only [map_zero]

theorem hasSubst_powerSeriesInVariable {σ R : Type*} [Fintype σ] [CommRing R]
    (φ : σ → PowerSeries R) (hφ : ∀ j, PowerSeries.constantCoeff (R := R) (φ j) = 0) :
    MvPowerSeries.HasSubst (fun j => powerSeriesInVariable R j (φ j)) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro j
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_powerSeriesInVariable]
  simpa only [Finsupp.zero_apply, Finsupp.single_zero, ite_true,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] using hφ j

theorem subst_powerSeriesInVariable {σ τ R : Type*} [CommRing R]
    (a : σ → MvPowerSeries τ R) (ha : MvPowerSeries.HasSubst a) (j : σ)
    (p : PowerSeries R) :
    MvPowerSeries.subst a (powerSeriesInVariable R j p) =
      MvPowerSeries.subst (fun _ : Unit => a j) p := by
  have hj : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X j)
  simpa only [powerSeriesInVariable, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.subst_X ha] using MvPowerSeries.subst_comp_subst_apply hj ha p

theorem powerSeriesInVariable_subst {σ R : Type*} [CommRing R] (j : σ)
    (p q : PowerSeries R) (hq : PowerSeries.constantCoeff (R := R) q = 0) :
    powerSeriesInVariable R j (MvPowerSeries.subst (fun _ : Unit => q) p) =
      MvPowerSeries.subst (fun _ : Unit => powerSeriesInVariable R j q) p := by
  have hq' : MvPowerSeries.HasSubst (fun _ : Unit => q) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hq)
  have hj : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X j)
  simpa only [powerSeriesInVariable, MvPowerSeries.substAlgHom_apply] using
    MvPowerSeries.subst_comp_subst_apply hq' hj p

theorem subst_separate_powerSeriesInVariable {σ R : Type*} [Fintype σ] [CommRing R]
    (φ : σ → PowerSeries R) (hφ : ∀ j, PowerSeries.constantCoeff (R := R) (φ j) = 0)
    (j : σ) (p : PowerSeries R) :
    MvPowerSeries.subst (fun i => powerSeriesInVariable R i (φ i)) (powerSeriesInVariable R j p) =
      powerSeriesInVariable R j (MvPowerSeries.subst (fun _ : Unit => φ j) p) :=
  (subst_powerSeriesInVariable _ (hasSubst_powerSeriesInVariable φ hφ) j p).trans
    (powerSeriesInVariable_subst j p (φ j) (hφ j)).symm

theorem subst_perm_powerSeriesInVariable {ι R : Type*} [Fintype ι] [CommRing R]
    (σ : Equiv.Perm ι) (j : ι) (p : PowerSeries R) :
    MvPowerSeries.subst (fun i => (MvPowerSeries.X (σ.symm i) : MvPowerSeries ι R))
        (powerSeriesInVariable R j p) = powerSeriesInVariable R (σ.symm j) p := by
  have ha : MvPowerSeries.HasSubst
      (fun i => (MvPowerSeries.X (σ.symm i) : MvPowerSeries ι R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => MvPowerSeries.constantCoeff_X (σ.symm i))
  simpa only [powerSeriesInVariable, MvPowerSeries.substAlgHom_apply] using
    subst_powerSeriesInVariable _ ha j p

theorem seeded_separate_sum_eq {ι σ R S : Type*} [Fintype ι] [Fintype σ]
    [CommRing R] [CommRing S] (g : R →+* S) (a : ι → R)
    (p : ι → σ → PowerSeries R) (π : Equiv.Perm σ) (φ H : σ → PowerSeries S)
    (hφ : ∀ j, PowerSeries.constantCoeff (R := S) (φ j) = 0) :
    (∏ j, powerSeriesInVariable S j (H j)) *
      MvPowerSeries.subst (fun j => powerSeriesInVariable S j (φ j))
        (MvPowerSeries.map (σ := σ) g
          (MvPowerSeries.subst (fun j => (MvPowerSeries.X (π.symm j) : MvPowerSeries σ R))
            (∑ i, MvPowerSeries.C (σ := σ) (R := R) (a i) * ∏ j, powerSeriesInVariable R j (p i j)))) =
      ∑ i, MvPowerSeries.C (σ := σ) (R := S) (g (a i)) *
        ∏ j, powerSeriesInVariable S j
          (H j * MvPowerSeries.subst (fun _ : Unit => φ j) (PowerSeries.map g (p i (π j)))) := by
  have hπ : MvPowerSeries.HasSubst
      (fun j => (MvPowerSeries.X (π.symm j) : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun j => MvPowerSeries.constantCoeff_X (π.symm j))
  have hΦ := hasSubst_powerSeriesInVariable φ hφ
  have hCπ (r : R) : MvPowerSeries.substAlgHom (R := R) hπ (MvPowerSeries.C (σ := σ) (R := R) r) =
      MvPowerSeries.C (σ := σ) (R := R) r := by
    simpa only [MvPowerSeries.c_eq_algebraMap] using
      (MvPowerSeries.substAlgHom (R := R) hπ).commutes r
  have hCΦ (r : S) : MvPowerSeries.substAlgHom (R := S) hΦ (MvPowerSeries.C (σ := σ) (R := S) r) =
      MvPowerSeries.C (σ := σ) (R := S) r := by
    simpa only [MvPowerSeries.c_eq_algebraMap] using
      (MvPowerSeries.substAlgHom (R := S) hΦ).commutes r
  have hterm (j : σ) (q : PowerSeries R) :
      MvPowerSeries.substAlgHom (R := S) hΦ
        (MvPowerSeries.map (σ := σ) g
          (MvPowerSeries.substAlgHom (R := R) hπ (powerSeriesInVariable R j q))) =
        powerSeriesInVariable S (π.symm j)
          (MvPowerSeries.subst (fun _ : Unit => φ (π.symm j)) (PowerSeries.map g q)) := by
    simp only [MvPowerSeries.substAlgHom_apply, subst_perm_powerSeriesInVariable,
      map_powerSeriesInVariable, subst_separate_powerSeriesInVariable φ hφ]
  have hprod (i : ι) :
      (∏ j, powerSeriesInVariable S (π.symm j)
        (MvPowerSeries.subst (fun _ : Unit => φ (π.symm j)) (PowerSeries.map g (p i j)))) =
      ∏ j, powerSeriesInVariable S j
        (MvPowerSeries.subst (fun _ : Unit => φ j) (PowerSeries.map g (p i (π j)))) := by
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.prod_comp π (fun j => powerSeriesInVariable S (π.symm j)
        (MvPowerSeries.subst (fun _ : Unit => φ (π.symm j)) (PowerSeries.map g (p i j))))).symm
  rw [← MvPowerSeries.substAlgHom_apply hπ, ← MvPowerSeries.substAlgHom_apply hΦ]
  simp only [map_sum, map_mul, map_prod, hCπ, hCΦ, MvPowerSeries.map_C, hterm, hprod]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.prod_mul_distrib]
  ring

end DirichletL
