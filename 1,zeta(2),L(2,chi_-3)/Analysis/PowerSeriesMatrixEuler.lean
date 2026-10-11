import Arithmetic.PowerSeriesEuler

/-!
Matrix product rules used in the regular-system specialization of CDT v2
`lem_Shidlovsky`, supplied TeX 2910-2935. Meanings and edge checks precede
-/

namespace DirichletL

open scoped Matrix

theorem powerSeriesEuler_matrix_mul {ι σ τ R : Type*} [Fintype σ] [CommRing R]
    (M : Matrix ι σ (PowerSeries R)) (N : Matrix σ τ (PowerSeries R)) :
    (M * N).map (powerSeriesEuler R) =
      M.map (powerSeriesEuler R) * N + M * N.map (powerSeriesEuler R) := by
  classical
  funext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  simp only [mul_comm, add_comm]

theorem powerSeriesEuler_matrix_mulVec {ι σ R : Type*} [Fintype σ] [CommRing R]
    (M : Matrix ι σ (PowerSeries R)) (f : σ → PowerSeries R) :
    (fun i => powerSeriesEuler R ((M *ᵥ f) i)) =
      M.map (powerSeriesEuler R) *ᵥ f +
        M *ᵥ (fun i => powerSeriesEuler R (f i)) := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib, Matrix.map_apply]
  simp only [mul_comm, add_comm]

theorem constantCoeff_powerSeriesEuler_matrix {ι σ R : Type*} [CommRing R]
    (M : Matrix ι σ (PowerSeries R)) :
    (M.map (powerSeriesEuler R)).map (PowerSeries.constantCoeff (R := R)) = 0 := by
  funext i j
  change PowerSeries.constantCoeff (R := R) (powerSeriesEuler R (M i j)) = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_powerSeriesEuler,
    Nat.cast_zero, zero_mul]

end DirichletL
