import Analysis.MinimumOrderMinors

/-!
Normalization by a minimum-order minor for the regular-system specialization
of CDT v2 `lem_Shidlovsky`, supplied TeX 2910-2935. Declaration meanings,
native interfaces, and edge checks are in
-/

namespace DirichletL

open scoped Matrix

theorem matrix_mul_left_cancel_of_det_ne_zero {ι σ R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] [IsDomain R]
    (M : Matrix ι ι R) (hM : M.det ≠ 0) {U V : Matrix ι σ R}
    (h : M * U = M * V) : U = V := by
  have ha := congrArg (fun N => M.adjugate * N) h
  simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
    Matrix.one_mul] at ha
  funext i j
  exact mul_left_cancel₀ hM (congrFun (congrFun ha i) j)

theorem cramer_submatrix_eq_det_update_selection {ι σ R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (T : Matrix ι σ R)
    (J : ι → σ) (i : ι) (j : σ) :
    (T.submatrix id J).cramer (T.col j) i =
      (T.submatrix id (Function.update J i j)).det := by
  rw [Matrix.cramer_apply]
  congr 1
  funext a b
  by_cases h : b = i
  · subst b
    simp [Matrix.updateCol_apply, Matrix.submatrix_apply, Matrix.col]
  · simp [Matrix.updateCol_apply, Matrix.submatrix_apply, h, Ne.symm h]

theorem exists_regular_normalization_of_minimum_order_minor {ι σ K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] (T : Matrix ι σ (PowerSeries K))
    (J : ι → σ) (hJ : (T.submatrix id J).det ≠ 0)
    (hmin : ∀ I : ι → σ, (T.submatrix id J).det.order ≤
      (T.submatrix id I).det.order) :
    ∃ B : Matrix ι σ (PowerSeries K), T.submatrix id J * B = T ∧
      B.submatrix id J = 1 := by
  classical
  let M := T.submatrix id J
  have hdiv (i : ι) (j : σ) : M.det ∣ M.cramer (T.col j) i := by
    apply (powerSeries_dvd_iff_order_le _ _).mpr
    rw [show M = T.submatrix id J from rfl,
      cramer_submatrix_eq_det_update_selection]
    exact hmin _
  choose B hB using hdiv
  change Matrix ι σ (PowerSeries K) at B
  have hTB : M * B = T := by
    funext i j
    apply mul_left_cancel₀ hJ
    calc
      M.det * (M * B) i j = (M *ᵥ (fun k => M.det * B k j)) i := by
        simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (M *ᵥ M.cramer (T.col j)) i := by
        rw [show (fun k => M.det * B k j) = M.cramer (T.col j) from
          funext (fun k => (hB k j).symm)]
      _ = M.det * T i j := by rw [Matrix.mulVec_cramer]; rfl
  refine ⟨B, hTB, ?_⟩
  apply matrix_mul_left_cancel_of_det_ne_zero M hJ
  rw [Matrix.mul_one]
  have hs := congrArg (fun N : Matrix ι σ (PowerSeries K) => N.submatrix id J) hTB
  simpa only [Matrix.submatrix_mul _ _ id id J Function.bijective_id,
    Matrix.submatrix_id_id] using hs

theorem exists_regular_normalization_of_linearIndependent_rows {ι σ K : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [Field K]
    (T : Matrix ι σ (PowerSeries K))
    (hT : LinearIndependent (FractionRing (PowerSeries K))
      (fun i j => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (T i j))) :
    ∃ (J : ι → σ) (B : Matrix ι σ (PowerSeries K)),
      (T.submatrix id J).det ≠ 0 ∧
      (∀ I : ι → σ, (T.submatrix id J).det.order ≤ (T.submatrix id I).det.order) ∧
      T.submatrix id J * B = T ∧ B.submatrix id J = 1 := by
  obtain ⟨J, hJ, hmin⟩ := exists_minimum_order_minor_of_linearIndependent_rows T hT
  obtain ⟨B, hTB, hBJ⟩ := exists_regular_normalization_of_minimum_order_minor T J hJ hmin
  exact ⟨J, B, hJ, hmin, hTB, hBJ⟩

end DirichletL
