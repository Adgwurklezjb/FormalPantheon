import Analysis.AuxiliaryLexSelection

/-!
Canonical variable permutation for CDT v2's seeding step, supplied TeX
3998-4028. The exponent acts by sigma and the variables by sigma inverse.
-/

namespace DirichletL

open scoped Classical

theorem degree_perm_exponent {ι : Type*} [Fintype ι]
    (n : ι →₀ ℕ) (σ : Equiv.Perm ι) :
    (Finsupp.equivFunOnFinite.symm (fun j => n (σ j))).degree = n.degree := by
  have hdeg (p : ι →₀ ℕ) : p.degree = ∑ j, p j :=
    Finsupp.sum_fintype p (fun _ k => k) (fun _ => rfl)
  rw [hdeg, hdeg]
  change (∑ j, n (σ j)) = ∑ j, n j
  exact Equiv.sum_comp σ n

theorem coeff_subst_perm {ι R : Type*} [Fintype ι] [CommRing R]
    (F : MvPowerSeries ι R) (σ : Equiv.Perm ι) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff (R := R) (Finsupp.equivFunOnFinite.symm (fun j => n (σ j)))
        (MvPowerSeries.subst (fun i => (MvPowerSeries.X (σ.symm i) : MvPowerSeries ι R)) F) =
      MvPowerSeries.coeff (R := R) n F := by
  have ha : MvPowerSeries.HasSubst
      (fun i => (MvPowerSeries.X (σ.symm i) : MvPowerSeries ι R)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (fun i => MvPowerSeries.constantCoeff_X (σ.symm i))
  have hprod (e : ι →₀ ℕ) :
      e.prod (fun i k => (MvPowerSeries.X (σ.symm i) : MvPowerSeries ι R) ^ k) =
        MvPowerSeries.monomial (R := R)
          (Finsupp.equivFunOnFinite.symm (fun j => e (σ j))) 1 := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPowerSeries.monomial_one_eq,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    change (∏ i, (MvPowerSeries.X (σ.symm i) : MvPowerSeries ι R) ^ e i) =
      ∏ j, MvPowerSeries.X j ^ e (σ j)
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.prod_comp σ
        (fun i => (MvPowerSeries.X (σ.symm i) : MvPowerSeries ι R) ^ e i)).symm
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ n]
  · rw [hprod, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro e he
    have hne : Finsupp.equivFunOnFinite.symm (fun j => n (σ j)) ≠
        Finsupp.equivFunOnFinite.symm (fun j => e (σ j)) := by
      intro h
      apply he
      ext i
      have hi := congrArg (fun p : ι →₀ ℕ => p (σ.symm i)) h
      simpa only [Finsupp.coe_equivFunOnFinite_symm, Equiv.apply_symm_apply] using hi.symm
    rw [hprod, MvPowerSeries.coeff_monomial, if_neg hne, smul_zero]

theorem exists_minimum_coefficient_subst_perm_monotone {d : ℕ} {R : Type*} [CommRing R]
    (F : MvPowerSeries (Fin d) R) (hF : F ≠ 0) :
    ∃ (n : Fin d →₀ ℕ) (σ : Equiv.Perm (Fin d)),
      MvPowerSeries.coeff (R := R) n F ≠ 0 ∧
      (∀ e : Fin d →₀ ℕ, e.degree < n.degree → MvPowerSeries.coeff (R := R) e F = 0) ∧
      Monotone (fun j => n (σ j)) ∧
      let p := Finsupp.equivFunOnFinite.symm (fun j => n (σ j))
      let G := MvPowerSeries.subst
        (fun i => (MvPowerSeries.X (σ.symm i) : MvPowerSeries (Fin d) R)) F
      MvPowerSeries.coeff (R := R) p G = MvPowerSeries.coeff (R := R) n F ∧
      (∀ e : Fin d →₀ ℕ, e.degree < p.degree → MvPowerSeries.coeff (R := R) e G = 0) ∧
      ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) e G ≠ 0 → e.degree = p.degree →
        toLex p ≤ toLex e := by
  obtain ⟨n, σ, hn, hmin, hmono, hleast⟩ := exists_minimal_total_exponent_monotone_lex F hF
  have hinverse (e : Fin d →₀ ℕ) :
      Finsupp.equivFunOnFinite.symm
        (fun j => (Finsupp.equivFunOnFinite.symm (fun i => e (σ.symm i))) (σ j)) = e := by
    ext j
    change e (σ.symm (σ j)) = e j
    rw [Equiv.symm_apply_apply]
  have hcoeff (e : Fin d →₀ ℕ) :
      MvPowerSeries.coeff (R := R) e
          (MvPowerSeries.subst (fun i => (MvPowerSeries.X (σ.symm i) :
            MvPowerSeries (Fin d) R)) F) =
        MvPowerSeries.coeff (R := R) (Finsupp.equivFunOnFinite.symm (fun i => e (σ.symm i))) F := by
    simpa only [hinverse] using coeff_subst_perm F σ
      (Finsupp.equivFunOnFinite.symm (fun i => e (σ.symm i)))
  refine ⟨n, σ, hn, hmin, hmono, coeff_subst_perm F σ n, ?_, ?_⟩
  · intro e he
    rw [hcoeff]
    apply hmin
    simpa only [degree_perm_exponent] using he
  · intro e he hdeg
    have he' : MvPowerSeries.coeff (R := R)
        (Finsupp.equivFunOnFinite.symm (fun i => e (σ.symm i))) F ≠ 0 := by
      simpa only [hcoeff] using he
    have hdeg' : (Finsupp.equivFunOnFinite.symm (fun i => e (σ.symm i))).degree =
        n.degree := by
      simpa only [degree_perm_exponent] using hdeg
    simpa only [hinverse] using hleast
      (Finsupp.equivFunOnFinite.symm (fun i => e (σ.symm i))) he' hdeg' σ

end DirichletL
