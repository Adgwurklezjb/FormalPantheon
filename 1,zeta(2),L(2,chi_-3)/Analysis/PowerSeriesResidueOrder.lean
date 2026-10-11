import Analysis.PowerSeriesOrderBounds

/-!
The residue step for CDT v2 `lem_Shidlovsky`; meanings, native interfaces,
-/

namespace DirichletL

open scoped Matrix

theorem powerSeriesEulerSystem_leading_coefficient {ι R : Type*}
    [Fintype ι] [CommRing R] (H : Matrix ι ι (PowerSeries R)) (Y : ι → PowerSeries R)
    (s : ℕ) (hθ : ∀ i, powerSeriesEuler R (Y i) = ∑ j, H i j * Y j)
    (hlow : ∀ i k, k < s → PowerSeries.coeff (R := R) k (Y i) = 0) :
    (fun i j => PowerSeries.constantCoeff (R := R) (H i j)) *ᵥ
        (fun i => PowerSeries.coeff (R := R) s (Y i)) =
      (s : R) • (fun i => PowerSeries.coeff (R := R) s (Y i)) := by
  classical
  funext i
  have h := congrArg (PowerSeries.coeff (R := R) s) (hθ i)
  rw [coeff_powerSeriesEuler, map_sum] at h
  change ∑ j, PowerSeries.constantCoeff (R := R) (H i j) * PowerSeries.coeff (R := R) s (Y j) = _
  change _ = (s : R) * PowerSeries.coeff (R := R) s (Y i)
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  exact (coeff_mul_eq_constantCoeff_mul (H i j) (Y j) s (hlow j)).symm

theorem exists_leading_coefficient_powerSeries_family {ι R : Type*} [CommRing R]
    (Y : ι → PowerSeries R) (hY : Y ≠ 0) :
    ∃ s : ℕ, (fun i => PowerSeries.coeff (R := R) s (Y i)) ≠ 0 ∧
      ∀ i k, k < s → PowerSeries.coeff (R := R) k (Y i) = 0 := by
  classical
  have hex : ∃ s : ℕ, (fun i => PowerSeries.coeff (R := R) s (Y i)) ≠ 0 := by
    by_contra! h
    apply hY
    funext i
    ext n
    simpa using congrFun (h n) i
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro i k hk
  have hz : (fun j => PowerSeries.coeff (R := R) k (Y j)) = 0 :=
    not_ne_iff.mp (Nat.find_min hex hk)
  simpa using congrFun hz i

theorem powerSeriesEulerSystem_hasEigenvector {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] (H : Matrix ι ι (PowerSeries K))
    (Y : ι → PowerSeries K) (s : ℕ)
    (hθ : ∀ i, powerSeriesEuler K (Y i) = ∑ j, H i j * Y j)
    (hlow : ∀ i k, k < s → PowerSeries.coeff (R := K) k (Y i) = 0)
    (hv : (fun i => PowerSeries.coeff (R := K) s (Y i)) ≠ 0) :
    Module.End.HasEigenvector
      (Matrix.toLinAlgEquiv' (fun i j => PowerSeries.constantCoeff (R := K) (H i j)))
      (s : K) (fun i => PowerSeries.coeff (R := K) s (Y i)) := by
  refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv⟩
  rw [Matrix.toLinAlgEquiv'_apply]
  exact powerSeriesEulerSystem_leading_coefficient H Y s hθ hlow

theorem isRoot_of_powerSeriesEulerSystem_annihilator {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] (H : Matrix ι ι (PowerSeries K))
    (Y : ι → PowerSeries K) (p : Polynomial K) (s : ℕ)
    (hp : Polynomial.aeval (H.map (PowerSeries.constantCoeff (R := K))) p = 0)
    (hθ : ∀ i, powerSeriesEuler K (Y i) = ∑ j, H i j * Y j)
    (hlow : ∀ i k, k < s → PowerSeries.coeff (R := K) k (Y i) = 0)
    (hv : (fun i => PowerSeries.coeff (R := K) s (Y i)) ≠ 0) :
    p.IsRoot (s : K) := by
  let A : Matrix ι ι K := fun i j => PowerSeries.constantCoeff (R := K) (H i j)
  let e : Matrix ι ι K ≃ₐ[K] Module.End K (ι → K) := Matrix.toLinAlgEquiv'
  have ha : Polynomial.aeval (e A) p = 0 := by
    calc
      Polynomial.aeval (e A) p = e (Polynomial.aeval A p) :=
        Polynomial.aeval_algHom_apply e A p
      _ = 0 := by rw [show Polynomial.aeval A p = 0 from hp, map_zero]
  have hev := powerSeriesEulerSystem_hasEigenvector H Y s hθ hlow hv
  have hz : p.eval (s : K) • (fun i => PowerSeries.coeff (R := K) s (Y i)) = 0 := by
    rw [← Module.End.aeval_apply_of_hasEigenvector hev, ha]
    rfl
  exact (smul_eq_zero.mp hz).resolve_right hv

theorem exists_nat_lt_bound_polynomial_roots {K : Type*} [Field K] [CharZero K]
    (p : Polynomial K) (hp : p ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, p.IsRoot (n : K) → n < N := by
  have hs : Set.Finite {n : ℕ | p.IsRoot (n : K)} :=
    (Polynomial.finite_setOf_isRoot hp).preimage Nat.cast_injective.injOn
  obtain ⟨B, hB⟩ := hs.bddAbove
  refine ⟨B + 1, ?_⟩
  intro n hn
  exact (hB hn).trans_lt (Nat.lt_succ_self B)

theorem exists_component_order_lt_of_eulerSystem_annihilator {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] (H : Matrix ι ι (PowerSeries K))
    (Y : ι → PowerSeries K) (p : Polynomial K) (N : ℕ)
    (hroots : ∀ n : ℕ, p.IsRoot (n : K) → n < N)
    (hp : Polynomial.aeval (H.map (PowerSeries.constantCoeff (R := K))) p = 0)
    (hθ : ∀ i, powerSeriesEuler K (Y i) = ∑ j, H i j * Y j) (hY : Y ≠ 0) :
    ∃ i, Y i ≠ 0 ∧ (Y i).order < (N : ℕ∞) := by
  classical
  obtain ⟨s, hv, hlow⟩ := exists_leading_coefficient_powerSeries_family Y hY
  have hs := hroots s (isRoot_of_powerSeriesEulerSystem_annihilator H Y p s hp hθ hlow hv)
  have hex : ∃ i, PowerSeries.coeff (R := K) s (Y i) ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_, ?_⟩
  · intro hz
    apply hi
    rw [hz, map_zero]
  · exact (PowerSeries.order_le s hi).trans_lt (by exact_mod_cast hs)

end DirichletL
