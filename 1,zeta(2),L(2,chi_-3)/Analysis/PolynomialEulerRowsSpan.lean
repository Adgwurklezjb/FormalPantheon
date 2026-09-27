import Analysis.PolynomialEulerRows

/-!
Stability of the derivative-row span in the regular-system specialization
of CDT v2 `lem_Shidlovsky`, supplied TeX 2910-2935. Declaration meanings,
-/

namespace DirichletL

open scoped Matrix

theorem polynomialEulerRows_connection {σ R : Type*} [Fintype σ] [CommRing R]
    (q : Polynomial R) (C : Matrix σ σ (Polynomial R)) (P : σ → Polynomial R)
    (A : Matrix σ σ (PowerSeries R))
    (hA : ∀ i j, (q : PowerSeries R) * A i j = (C i j : PowerSeries R))
    (n : ℕ) (j : σ) :
    (q : PowerSeries R) * (powerSeriesEuler R (polynomialEulerRows q C P n j : PowerSeries R) +
      ∑ k, (polynomialEulerRows q C P n k : PowerSeries R) * A k j) =
      (polynomialEulerRows q C P (n + 1) j : PowerSeries R) +
        (n : PowerSeries R) * powerSeriesEuler R (q : PowerSeries R) *
          (polynomialEulerRows q C P n j : PowerSeries R) := by
  classical
  have hsum : ((∑ k, polynomialEulerRows q C P n k * C k j : Polynomial R) : PowerSeries R) =
      ∑ k, (polynomialEulerRows q C P n k : PowerSeries R) * (C k j : PowerSeries R) := by
    change Polynomial.coeToPowerSeries.ringHom
      (∑ k, polynomialEulerRows q C P n k * C k j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact Polynomial.coe_mul _ _
  have hmul : (q : PowerSeries R) *
      (∑ k, (polynomialEulerRows q C P n k : PowerSeries R) * A k j) =
      ∑ k, (polynomialEulerRows q C P n k : PowerSeries R) * (C k j : PowerSeries R) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← hA k j]
    ring
  rw [mul_add, hmul]
  change _ = Polynomial.coeToPowerSeries.ringHom (polynomialEulerRows q C P (n + 1) j) + _
  simp only [polynomialEulerRows_succ, map_sub, map_add, map_mul, map_natCast,
    RingHom.map_vecMul, Polynomial.coeToPowerSeries.ringHom_apply, coe_polynomialEuler,
    Matrix.vecMul, dotProduct, Matrix.map_apply, Function.comp_apply]
  rw [hsum]
  ring

theorem polynomialEulerRows_fraction_span_stable {σ K : Type*} [Fintype σ] [Field K]
    (q : Polynomial K) (C : Matrix σ σ (Polynomial K)) (P : σ → Polynomial K)
    (A : Matrix σ σ (PowerSeries K)) (hq : (q : PowerSeries K) ≠ 0)
    (hA : ∀ i j, (q : PowerSeries K) * A i j = (C i j : PowerSeries K))
    (r : ℕ)
    (hdep : (fun j => algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
        (polynomialEulerRows q C P r j : PowerSeries K)) ∈
      Submodule.span (FractionRing (PowerSeries K))
        (Set.range (fun i : Fin r => fun j =>
          algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (polynomialEulerRows q C P i.val j : PowerSeries K)))) (i : Fin r) :
    (fun j => algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
      (powerSeriesEuler K (polynomialEulerRows q C P i.val j : PowerSeries K) +
        ∑ k, (polynomialEulerRows q C P i.val k : PowerSeries K) * A k j)) ∈
      Submodule.span (FractionRing (PowerSeries K))
        (Set.range (fun i : Fin r => fun j =>
          algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
            (polynomialEulerRows q C P i.val j : PowerSeries K))) := by
  classical
  let φ := algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
  let v : ℕ → σ → FractionRing (PowerSeries K) :=
    fun n j => φ (polynomialEulerRows q C P n j : PowerSeries K)
  let W := Submodule.span (FractionRing (PowerSeries K)) (Set.range (fun i : Fin r => v i.val))
  have hv : v i.val ∈ W := Submodule.subset_span ⟨i, rfl⟩
  have hnext : v (i.val + 1) ∈ W := by
    by_cases hi : i.val + 1 < r
    · exact Submodule.subset_span ⟨⟨i.val + 1, hi⟩, rfl⟩
    · have hir : i.val + 1 = r := by omega
      rw [hir]
      exact hdep
  have hqφ : φ (q : PowerSeries K) ≠ 0 := by
    intro hz
    apply hq
    exact IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
      (hz.trans (map_zero φ).symm)
  apply (W.smul_mem_iff hqφ).mp
  have he : φ (q : PowerSeries K) •
      (fun j => φ (powerSeriesEuler K (polynomialEulerRows q C P i.val j : PowerSeries K) +
        ∑ k, (polynomialEulerRows q C P i.val k : PowerSeries K) * A k j)) =
      v (i.val + 1) + φ ((i.val : PowerSeries K) * powerSeriesEuler K (q : PowerSeries K)) •
        v i.val := by
    funext j
    have h := congrArg φ (polynomialEulerRows_connection q C P A hA i.val j)
    simpa only [map_add, map_mul] using h
  rw [he]
  exact W.add_mem hnext (W.smul_mem _ hv)

end DirichletL
