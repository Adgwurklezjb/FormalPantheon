import Analysis.PowerSeriesOrderBounds

/-!
Polynomial-minor degree bounds in the regular-system specialization of CDT v2
`lem_Shidlovsky`, supplied TeX 2910-2935. Declaration meanings and edge
-/

namespace DirichletL

theorem natDegree_matrix_det_le {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (M : Matrix ι ι (Polynomial R)) (E : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ E) :
    M.det.natDegree ≤ Fintype.card ι * E := by
  classical
  rw [Matrix.det_apply']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e _
  calc
    _ ≤ (((Equiv.Perm.sign e : ℤ) : Polynomial R)).natDegree +
        (∏ i, M (e i) i).natDegree := Polynomial.natDegree_mul_le
    _ = (∏ i, M (e i) i).natDegree := by rw [Polynomial.natDegree_intCast, zero_add]
    _ ≤ ∑ i, (M (e i) i).natDegree :=
      Polynomial.natDegree_prod_le Finset.univ (fun i => M (e i) i)
    _ ≤ ∑ _i : ι, E := Finset.sum_le_sum (fun i _ => hM (e i) i)
    _ = Fintype.card ι * E := by simp

theorem order_polynomial_minor_le {ι σ K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] (T : Matrix ι σ (Polynomial K))
    (J : ι → σ) (E : ℕ) (hT : ∀ i j, (T i j).natDegree ≤ E)
    (hJ : ((T.map Polynomial.coeToPowerSeries.ringHom).submatrix id J).det ≠ 0) :
    ((T.map Polynomial.coeToPowerSeries.ringHom).submatrix id J).det.order ≤
      (Fintype.card ι * E : ℕ) := by
  let δ := (T.submatrix id J).det
  have he : ((T.map Polynomial.coeToPowerSeries.ringHom).submatrix id J).det =
      (δ : PowerSeries K) := by
    rw [Matrix.submatrix_map]
    exact (RingHom.map_det Polynomial.coeToPowerSeries.ringHom (T.submatrix id J)).symm
  have hδ : δ ≠ 0 := by
    intro hz
    apply hJ
    rw [he, hz, Polynomial.coe_zero]
  rw [he]
  exact (order_coe_polynomial_le_natDegree δ hδ).trans
    (by exact_mod_cast natDegree_matrix_det_le (T.submatrix id J) E (fun i j => hT i (J j)))

end DirichletL
