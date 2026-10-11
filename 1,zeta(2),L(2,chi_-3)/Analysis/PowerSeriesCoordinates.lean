import Comparator.Statement

/-!
Canonical products in separate variables for CDT v2,
supplied TeX 2910-2935 and 3965-3998.
-/

noncomputable section

namespace DirichletL

open scoped Classical

/-- Put a univariate series in one coordinate by valid canonical substitution. -/
def powerSeriesInVariable {σ : Type*} (R : Type*) [CommRing R] (j : σ) :
    PowerSeries R →ₐ[R] MvPowerSeries σ R :=
  MvPowerSeries.substAlgHom (R := R) (a := fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries σ R))
    (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (fun _ : Unit => MvPowerSeries.constantCoeff_X j))

theorem coeff_powerSeriesInVariable {σ R : Type*} [CommRing R]
    (j : σ) (f : PowerSeries R) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff (R := R) n (powerSeriesInVariable R j f) =
      if n = Finsupp.single j (n j) then PowerSeries.coeff (R := R) (n j) f else 0 := by
  have ha : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X j : MvPowerSeries σ R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X j)
  have hpow (u : Unit →₀ ℕ) :
      u.prod (fun _ : Unit => fun k => (MvPowerSeries.X j : MvPowerSeries σ R) ^ k) =
        MvPowerSeries.X j ^ u () := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp
  rw [powerSeriesInVariable, MvPowerSeries.substAlgHom_apply, MvPowerSeries.coeff_subst ha]
  rw [finsum_eq_single _ (Finsupp.single () (n j))]
  · rw [hpow]
    simp only [Finsupp.single_eq_same, MvPowerSeries.coeff_X_pow, smul_eq_mul]
    change PowerSeries.coeff (R := R) (n j) f *
      (if n = Finsupp.single j (n j) then 1 else 0) = _
    split_ifs <;> simp
  · intro u hu
    rw [hpow, MvPowerSeries.coeff_X_pow, if_neg ?_, smul_zero]
    intro hn
    apply hu
    have hu0 : u () = n j := by
      simpa using (congrArg (fun e : σ →₀ ℕ => e j) hn).symm
    apply Finsupp.unique_ext
    simpa using hu0

theorem coeff_prod_powerSeriesInVariable {σ R : Type*} [Fintype σ] [CommRing R]
    (f : σ → PowerSeries R) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff (R := R) n (∏ j, powerSeriesInVariable R j (f j)) =
      ∏ j, PowerSeries.coeff (R := R) (n j) (f j) := by
  let v : σ →₀ (σ →₀ ℕ) :=
    Finsupp.equivFunOnFinite.symm (fun j => Finsupp.single j (n j))
  have hv : v ∈ Finset.finsuppAntidiag Finset.univ n := by
    apply Finset.mem_finsuppAntidiag.mpr
    exact ⟨by simpa only [v, Finsupp.coe_equivFunOnFinite_symm]
      using Finsupp.univ_sum_single n, Finset.subset_univ _⟩
  rw [MvPowerSeries.coeff_prod, Finset.sum_eq_single v]
  · simp [v, coeff_powerSeriesInVariable]
  · intro l hl hlv
    by_contra hnonzero
    have hcoord (j : σ) : l j = Finsupp.single j ((l j) j) := by
      by_contra hne
      apply hnonzero
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [coeff_powerSeriesInVariable, if_neg hne]
    have hsum : ∑ j, l j = n := (Finset.mem_finsuppAntidiag.mp hl).1
    have hn (i : σ) : n i = (l i) i := by
      calc
        n i = ∑ j, (l j) i := by
          simpa only [Finsupp.finset_sum_apply] using
            (congrArg (fun e : σ →₀ ℕ => e i) hsum).symm
        _ = ∑ j, (Finsupp.single j ((l j) j)) i :=
          Finset.sum_congr rfl (fun j _ => congrArg (fun e : σ →₀ ℕ => e i) (hcoord j))
        _ = (l i) i := by simp [Finsupp.single_apply]
    apply hlv
    apply Finsupp.ext
    intro i
    change l i = Finsupp.single i (n i)
    rw [hcoord i, hn i]
  · intro hnot
    exact (hnot hv).elim

theorem powerSeriesInVariable_monomial_one {σ R : Type*} [CommRing R]
    (j : σ) (k : ℕ) :
    powerSeriesInVariable R j (PowerSeries.monomial (R := R) k 1) = MvPowerSeries.X j ^ k := by
  change MvPowerSeries.substAlgHom (R := R) _
    (MvPowerSeries.monomial (R := R) (Finsupp.single () k) 1) = _
  rw [MvPowerSeries.substAlgHom_monomial]
  simp

theorem prod_powerSeriesInVariable_shift {σ R : Type*} [Fintype σ] [CommRing R]
    (f : σ → PowerSeries R) (k : σ → ℕ) :
    (∏ j, powerSeriesInVariable R j (PowerSeries.monomial (R := R) (k j) 1 * f j)) =
      MvPowerSeries.monomial (R := R) (Finsupp.equivFunOnFinite.symm k) 1 *
        ∏ j, powerSeriesInVariable R j (f j) := by
  simp_rw [map_mul, powerSeriesInVariable_monomial_one]
  rw [Finset.prod_mul_distrib, MvPowerSeries.monomial_one_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

end DirichletL
