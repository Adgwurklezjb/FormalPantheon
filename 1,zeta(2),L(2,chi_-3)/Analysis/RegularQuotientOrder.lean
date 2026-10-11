import Analysis.RegularQuotientSystem
import Analysis.MatrixPolynomialIntertwining
import Analysis.PowerSeriesResidueOrder

/-!
Uniform residue and determinant-order comparisons for the specialization of
CDT v2 `lem_Shidlovsky`, supplied TeX 2910-2935. The quantifiers, meanings,
-/

namespace DirichletL

open scoped Matrix

theorem exists_uniform_order_bound_regular_quotient {σ K : Type*}
    [Fintype σ] [DecidableEq σ] [Field K] [CharZero K]
    (A : Matrix σ σ (PowerSeries K)) :
    ∃ N : ℕ, ∀ (r : ℕ) (B : Matrix (Fin r) σ (PowerSeries K))
      (H : Matrix (Fin r) (Fin r) (PowerSeries K)) (J : Fin r → σ)
      (f : σ → PowerSeries K), B.submatrix id J = 1 →
      B.map (powerSeriesEuler K) + B * A = H * B →
      (fun i => powerSeriesEuler K (f i)) = A *ᵥ f → B *ᵥ f ≠ 0 →
      ∃ i, (B *ᵥ f) i ≠ 0 ∧ ((B *ᵥ f) i).order < (N : ℕ∞) := by
  let A₀ := A.map (PowerSeries.constantCoeff (R := K))
  obtain ⟨N, hN⟩ := exists_nat_lt_bound_polynomial_roots A₀.charpoly A₀.charpoly_monic.ne_zero
  refine ⟨N, ?_⟩
  intro r B H J f hBJ hB hf hY
  have hBJ₀ : (B.map (PowerSeries.constantCoeff (R := K))).submatrix id J = 1 := by
    rw [Matrix.submatrix_map, hBJ,
      Matrix.map_one _ (map_zero (PowerSeries.constantCoeff (R := K)))
        (map_one (PowerSeries.constantCoeff (R := K)))]
  have hp := matrix_aeval_charpoly_eq_zero_of_intertwining
    (H.map (PowerSeries.constantCoeff (R := K))) A₀ (B.map (PowerSeries.constantCoeff (R := K))) J hBJ₀
    (regular_quotient_residue_intertwining B A H hB)
  apply exists_component_order_lt_of_eulerSystem_annihilator H (B *ᵥ f) A₀.charpoly N hN hp
  · intro i
    exact congrFun (regular_quotient_solution B A H f hB hf) i
  · exact hY

theorem nat_le_det_order_add_of_normalization {ι σ K : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [Field K]
    (T B : Matrix ι σ (PowerSeries K)) (J : ι → σ)
    (hTB : T.submatrix id J * B = T) (f : σ → PowerSeries K) (L : ℕ)
    (hlow : ∀ i, (L : ℕ∞) ≤ ((T *ᵥ f) i).order) (i : ι) :
    (L : ℕ∞) ≤ (T.submatrix id J).det.order + ((B *ᵥ f) i).order := by
  let M := T.submatrix id J
  have hTf : T *ᵥ f = M *ᵥ (B *ᵥ f) := by
    rw [Matrix.mulVec_mulVec, hTB]
  have ha : M.adjugate *ᵥ (T *ᵥ f) = M.det • (B *ᵥ f) := by
    rw [hTf, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  have h := nat_le_order_sum_mul (M.adjugate i) (T *ᵥ f) L hlow
  change (L : ℕ∞) ≤ ((M.adjugate *ᵥ (T *ᵥ f)) i).order at h
  rw [ha] at h
  change (L : ℕ∞) ≤ (M.det * (B *ᵥ f) i).order at h
  rwa [PowerSeries.order_mul] at h

theorem exists_uniform_order_bound_stable_rows {σ K : Type*}
    [Fintype σ] [DecidableEq σ] [Field K] [CharZero K]
    (A : Matrix σ σ (PowerSeries K)) :
    ∃ N : ℕ, ∀ (r : ℕ) (T : Matrix (Fin r) σ (PowerSeries K))
      (f : σ → PowerSeries K) (L : ℕ),
      LinearIndependent (FractionRing (PowerSeries K))
        (T.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).row →
      (∀ i, (fun j => algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          ((T.map (powerSeriesEuler K) + T * A) i j)) ∈
        Submodule.span (FractionRing (PowerSeries K))
          (Set.range (T.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))).row)) →
      (fun i => powerSeriesEuler K (f i)) = A *ᵥ f → T *ᵥ f ≠ 0 →
      (∀ i, (L : ℕ∞) ≤ ((T *ᵥ f) i).order) →
      ∃ J : Fin r → σ, (T.submatrix id J).det ≠ 0 ∧
        L < (T.submatrix id J).det.order.toNat + N := by
  obtain ⟨N, hN⟩ := exists_uniform_order_bound_regular_quotient A
  refine ⟨N, ?_⟩
  intro r T f L hTI hstable hf hTf hlow
  obtain ⟨J, B, hJ, _, hTB, hBJ⟩ :=
    exists_regular_normalization_of_linearIndependent_rows T hTI
  let H := (B.map (powerSeriesEuler K) + B * A).submatrix id J
  have hB : B.map (powerSeriesEuler K) + B * A = H * B :=
    regular_quotient_euler_system T B A J hJ hTB hBJ hstable
  have hY : B *ᵥ f ≠ 0 := by
    intro hz
    apply hTf
    rw [← hTB, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero]
  obtain ⟨i, hi, hiN⟩ := hN r B H J f hBJ hB hf hY
  have h := nat_le_det_order_add_of_normalization T B J hTB f L hlow i
  rw [← PowerSeries.coe_toNat_order hJ, ← PowerSeries.coe_toNat_order hi] at h
  rw [← PowerSeries.coe_toNat_order hi] at hiN
  have h₁ : L ≤ (T.submatrix id J).det.order.toNat + ((B *ᵥ f) i).order.toNat := by
    exact_mod_cast h
  have h₂ : ((B *ᵥ f) i).order.toNat < N := by exact_mod_cast hiN
  exact ⟨J, hJ, h₁.trans_lt (Nat.add_lt_add_left h₂ _)⟩

end DirichletL
