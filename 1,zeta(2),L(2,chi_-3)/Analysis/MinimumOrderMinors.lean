import Analysis.PowerSeriesOrderBounds

/-!
The minor step for CDT v2 `lem_Shidlovsky`; meanings and native interfaces
-/

namespace DirichletL

theorem span_cols_eq_top_of_linearIndependent_rows {ι σ K : Type*}
    [Fintype ι] [Fintype σ] [Field K] (M : Matrix ι σ K)
    (hM : LinearIndependent K M.row) :
    Submodule.span K (Set.range M.col) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [← M.rank_eq_finrank_span_cols, hM.rank_matrix,
    Module.finrank_fintype_fun_eq_card]

theorem exists_det_submatrix_ne_zero_of_linearIndependent_rows {ι σ K : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [Field K] (M : Matrix ι σ K)
    (hM : LinearIndependent K M.row) :
    ∃ J : ι → σ, (M.submatrix id J).det ≠ 0 := by
  classical
  have hs := span_cols_eq_top_of_linearIndependent_rows M hM
  let b := Module.Basis.ofSpan hs.ge
  let e := b.indexEquiv (Pi.basisFun K ι)
  let v : ι → ι → K := fun i => b (e.symm i)
  have hv : LinearIndependent K v := b.linearIndependent.comp e.symm e.symm.injective
  have hb (i : ι) : v i ∈ Set.range M.col :=
    Module.Basis.ofSpan_subset hs.ge ⟨e.symm i, rfl⟩
  choose J hJ using hb
  have hc : (M.submatrix id J).col = v := by
    funext i
    exact hJ i
  have hcol : LinearIndependent K (M.submatrix id J).col := hc.symm ▸ hv
  exact ⟨J, ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcol)).ne_zero⟩

theorem exists_minimum_order_minor {ι σ K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] (M : Matrix ι σ (PowerSeries K))
    (hM : ∃ J : ι → σ, (M.submatrix id J).det ≠ 0) :
    ∃ J : ι → σ, (M.submatrix id J).det ≠ 0 ∧
      ∀ I : ι → σ, (M.submatrix id J).det.order ≤ (M.submatrix id I).det.order := by
  classical
  have hex : ∃ n : ℕ, ∃ J : ι → σ,
      (M.submatrix id J).det ≠ 0 ∧ (M.submatrix id J).det.order = (n : ℕ∞) := by
    obtain ⟨J, hJ⟩ := hM
    exact ⟨(M.submatrix id J).det.order.toNat, J, hJ,
      (PowerSeries.coe_toNat_order hJ).symm⟩
  obtain ⟨J, hJ, horder⟩ := Nat.find_spec hex
  refine ⟨J, hJ, ?_⟩
  intro I
  by_cases hI : (M.submatrix id I).det = 0
  · simp [hI]
  · have hn := Nat.find_min' hex ⟨I, hI, (PowerSeries.coe_toNat_order hI).symm⟩
    rw [horder, ← PowerSeries.coe_toNat_order hI]
    exact_mod_cast hn

theorem exists_minimum_order_minor_of_linearIndependent_rows {ι σ K : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [Field K]
    (M : Matrix ι σ (PowerSeries K))
    (hM : LinearIndependent (FractionRing (PowerSeries K))
      (fun i j => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (M i j))) :
    ∃ J : ι → σ, (M.submatrix id J).det ≠ 0 ∧
      ∀ I : ι → σ, (M.submatrix id J).det.order ≤ (M.submatrix id I).det.order := by
  let φ := algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
  obtain ⟨J, hJ⟩ := exists_det_submatrix_ne_zero_of_linearIndependent_rows
    (fun i j => φ (M i j)) hM
  apply exists_minimum_order_minor M
  refine ⟨J, ?_⟩
  intro hz
  apply hJ
  have hmap : (Matrix.submatrix (fun i j => φ (M i j)) id J).det =
      φ ((M.submatrix id J).det) := (RingHom.map_det φ (M.submatrix id J)).symm
  rw [hmap, hz, map_zero]

end DirichletL
