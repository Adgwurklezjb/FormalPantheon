import Analysis.PowerSeriesPolynomialIndependence

/-!
Polynomial descriptions of the shifted-series span in CDT v2,
`lem_Shidlovsky` (TeX 2910-2935) and the auxiliary template (TeX 3965-3998).
Meanings and edge checks precede these proofs in
-/

namespace DirichletL

theorem exists_polynomial_combination_of_mem_shifted_span {ι K : Type*}
    [Fintype ι] [Field K] (f : ι → PowerSeries K) (D : ℕ) (hD : 0 < D)
    (u : PowerSeries K)
    (hu : u ∈ Submodule.span K (Set.range (fun p : ι × Fin D =>
      PowerSeries.monomial (R := K) p.2.val 1 * f p.1))) :
    ∃ P : ι → Polynomial K, (∀ i, (P i).natDegree < D) ∧
      ∑ i, (P i : PowerSeries K) * f i = u := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hu
  let P : ι → Polynomial K := fun i => Polynomial.ofFn D (fun k => c (i, k))
  refine ⟨P, fun i => Polynomial.ofFn_natDegree_lt hD (fun k => c (i, k)), ?_⟩
  calc
    _ = ∑ i, ∑ k : Fin D, c (i, k) • (PowerSeries.monomial (R := K) k.val 1 * f i) := by
      apply Finset.sum_congr rfl
      intro i _
      change Polynomial.coeToPowerSeries.ringHom
        (Polynomial.ofFn D (fun k => c (i, k))) * f i = _
      rw [Polynomial.ofFn_eq_sum_monomial, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      change (Polynomial.monomial k.val (c (i, k)) : PowerSeries K) * f i = _
      rw [Polynomial.coe_monomial]
      have hm : PowerSeries.monomial (R := K) k.val (c (i, k)) =
          c (i, k) • PowerSeries.monomial (R := K) k.val 1 := by
        simpa only [smul_eq_mul, mul_one] using
          (PowerSeries.monomial (R := K) k.val).map_smul (c (i, k)) (1 : K)
      rw [hm, smul_mul_assoc]
    _ = ∑ p : ι × Fin D, c p • (PowerSeries.monomial (R := K) p.2.val 1 * f p.1) := by
      rw [Fintype.sum_prod_type]
    _ = u := hc

theorem order_lt_of_mem_shifted_span {ι K : Type*} [Fintype ι] [Field K]
    (f : ι → PowerSeries K) (D N : ℕ) (hD : 0 < D)
    (hbound : ∀ P : ι → Polynomial K, (∀ i, (P i).natDegree < D) →
      (∑ i, (P i : PowerSeries K) * f i) ≠ 0 →
        (∑ i, (P i : PowerSeries K) * f i).order < (N : ℕ∞))
    (u : PowerSeries K)
    (hu : u ∈ Submodule.span K (Set.range (fun p : ι × Fin D =>
      PowerSeries.monomial (R := K) p.2.val 1 * f p.1))) (hne : u ≠ 0) : u.order < (N : ℕ∞) := by
  obtain ⟨P, hP, he⟩ := exists_polynomial_combination_of_mem_shifted_span f D hD u hu
  rw [← he] at hne ⊢
  exact hbound P hP hne

end DirichletL
