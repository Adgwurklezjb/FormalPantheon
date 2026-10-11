import Analysis.RegularMinorNormalization
import Analysis.PowerSeriesMatrixEuler

/-!
A regular quotient of a stable row space in the specialization of CDT v2
`lem_Shidlovsky`, supplied TeX 2910-2935. Meanings, source interfaces, and
-/

namespace DirichletL

open scoped Matrix

theorem row_eq_selected_vecMul_of_mem_span {ι σ R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (T B : Matrix ι σ R)
    (J : ι → σ) (hTB : T.submatrix id J * B = T) (hBJ : B.submatrix id J = 1)
    (E : σ → R) (hE : E ∈ Submodule.span R (Set.range T.row)) :
    E = (fun i => E (J i)) ᵥ* B := by
  rw [← range_vecMulLinear] at hE
  obtain ⟨u, hu⟩ := hE
  change u ᵥ* T = E at hu
  let v := u ᵥ* T.submatrix id J
  have hv : E = v ᵥ* B := by
    rw [← hu, ← hTB, ← Matrix.vecMul_vecMul]
  have hs : (fun i => E (J i)) = v := by
    rw [hv]
    change v ᵥ* B.submatrix id J = v
    rw [hBJ, Matrix.vecMul_one]
  rw [hs, hv]

theorem row_eq_selected_vecMul_of_mem_fraction_span {ι σ K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] (T B : Matrix ι σ (PowerSeries K))
    (J : ι → σ) (hTB : T.submatrix id J * B = T) (hBJ : B.submatrix id J = 1)
    (E : σ → PowerSeries K)
    (hE : (fun j => algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (E j)) ∈
      Submodule.span (FractionRing (PowerSeries K))
        (Set.range (T.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).row)) :
    E = (fun i => E (J i)) ᵥ* B := by
  let φ := algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
  have hT : (T.map φ).submatrix id J * B.map φ = T.map φ := by
    have h := congrArg (fun N : Matrix ι σ (PowerSeries K) => N.map φ) hTB
    simpa only [Matrix.map_mul, Matrix.submatrix_map] using h
  have hB : (B.map φ).submatrix id J = 1 := by
    rw [Matrix.submatrix_map, hBJ, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have h := row_eq_selected_vecMul_of_mem_span (T.map φ) (B.map φ) J hT hB
    (fun j => φ (E j)) hE
  funext j
  apply IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
  simpa only [Matrix.vecMul, dotProduct, map_sum, map_mul, Matrix.map_apply] using congrFun h j

theorem regular_quotient_euler_system {ι σ K : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [Field K]
    (T B : Matrix ι σ (PowerSeries K)) (A : Matrix σ σ (PowerSeries K))
    (J : ι → σ) (hJ : (T.submatrix id J).det ≠ 0)
    (hTB : T.submatrix id J * B = T) (hBJ : B.submatrix id J = 1)
    (hstable : ∀ i,
      (fun j => algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
        ((T.map (powerSeriesEuler K) + T * A) i j)) ∈
      Submodule.span (FractionRing (PowerSeries K))
        (Set.range (T.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).row)) :
    B.map (powerSeriesEuler K) + B * A =
      (B.map (powerSeriesEuler K) + B * A).submatrix id J * B := by
  let M := T.submatrix id J
  let E := T.map (powerSeriesEuler K) + T * A
  let Q := B.map (powerSeriesEuler K) + B * A
  have hE : E = E.submatrix id J * B := by
    funext i j
    exact congrFun (row_eq_selected_vecMul_of_mem_fraction_span T B J hTB hBJ
      (E i) (hstable i)) j
  have hprod : E = M.map (powerSeriesEuler K) * B + M * Q := by
    change T.map (powerSeriesEuler K) + T * A =
      M.map (powerSeriesEuler K) * B + M * (B.map (powerSeriesEuler K) + B * A)
    rw [← hTB, powerSeriesEuler_matrix_mul, Matrix.mul_add, Matrix.mul_assoc, add_assoc]
  have hs : E.submatrix id J = M.map (powerSeriesEuler K) + M * Q.submatrix id J := by
    rw [hprod]
    change (M.map (powerSeriesEuler K) * B).submatrix id J +
      (M * Q).submatrix id J = _
    simp only [Matrix.submatrix_mul _ _ id id J Function.bijective_id,
      Matrix.submatrix_id_id, hBJ, Matrix.mul_one]
  apply matrix_mul_left_cancel_of_det_ne_zero M hJ
  apply add_left_cancel (a := M.map (powerSeriesEuler K) * B)
  calc
    _ = E := hprod.symm
    _ = E.submatrix id J * B := hE
    _ = _ := by rw [hs, Matrix.add_mul, Matrix.mul_assoc]

theorem regular_quotient_residue_intertwining {ι σ R : Type*}
    [Fintype ι] [Fintype σ] [CommRing R]
    (B : Matrix ι σ (PowerSeries R)) (A : Matrix σ σ (PowerSeries R))
    (H : Matrix ι ι (PowerSeries R))
    (h : B.map (powerSeriesEuler R) + B * A = H * B) :
    H.map (PowerSeries.constantCoeff (R := R)) * B.map (PowerSeries.constantCoeff (R := R)) =
      B.map (PowerSeries.constantCoeff (R := R)) * A.map (PowerSeries.constantCoeff (R := R)) := by
  have hc := congrArg (fun M : Matrix ι σ (PowerSeries R) =>
    M.map (PowerSeries.constantCoeff (R := R))) h
  change (B.map (powerSeriesEuler R) + B * A).map (PowerSeries.constantCoeff (R := R)) =
    (H * B).map (PowerSeries.constantCoeff (R := R)) at hc
  simp only [Matrix.map_add (PowerSeries.constantCoeff (R := R)) (map_add _),
    constantCoeff_powerSeriesEuler_matrix, zero_add, Matrix.map_mul] at hc
  exact hc.symm

theorem regular_quotient_solution {ι σ R : Type*}
    [Fintype ι] [Fintype σ] [CommRing R]
    (B : Matrix ι σ (PowerSeries R)) (A : Matrix σ σ (PowerSeries R))
    (H : Matrix ι ι (PowerSeries R)) (f : σ → PowerSeries R)
    (hB : B.map (powerSeriesEuler R) + B * A = H * B)
    (hf : (fun i => powerSeriesEuler R (f i)) = A *ᵥ f) :
    (fun i => powerSeriesEuler R ((B *ᵥ f) i)) = H *ᵥ (B *ᵥ f) := by
  rw [powerSeriesEuler_matrix_mulVec, hf, Matrix.mulVec_mulVec,
    ← Matrix.add_mulVec, hB, Matrix.mulVec_mulVec]

end DirichletL
