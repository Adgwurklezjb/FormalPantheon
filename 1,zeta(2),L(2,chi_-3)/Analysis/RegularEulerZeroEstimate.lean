import Analysis.RegularQuotientOrder
import Analysis.FirstLinearDependence
import Analysis.PolynomialMatrixDegree
import Analysis.PolynomialEulerRowsSolution
import Analysis.PolynomialEulerRowsSpan

/-!
A quantitative order estimate for regular Euler systems, specializing the
closed-system case of CDT v2 `lem_Shidlovsky`, supplied TeX 2910-2935.
The independently checked calculation, quantifiers, and edge cases precede
-/

namespace DirichletL

open scoped Matrix

theorem exists_powerSeries_matrix_of_polynomial_denominator {σ K : Type*} [Field K]
    (q : Polynomial K) (C : Matrix σ σ (Polynomial K)) (hq : q.coeff 0 ≠ 0) :
    ∃ A : Matrix σ σ (PowerSeries K), ∀ i j,
      (q : PowerSeries K) * A i j = (C i j : PowerSeries K) := by
  have hu : IsUnit (q : PowerSeries K) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe] using hq
  obtain ⟨u, hu⟩ := hu
  refine ⟨fun i j => (↑(u⁻¹) : PowerSeries K) * (C i j : PowerSeries K), ?_⟩
  intro i j
  rw [← hu, ← mul_assoc]
  simp

theorem powerSeriesEuler_system_of_cleared {σ K : Type*} [Fintype σ] [Field K]
    (q : Polynomial K) (C : Matrix σ σ (Polynomial K)) (A : Matrix σ σ (PowerSeries K))
    (hq : (q : PowerSeries K) ≠ 0)
    (hA : ∀ i j, (q : PowerSeries K) * A i j = (C i j : PowerSeries K))
    (f : σ → PowerSeries K)
    (hf : ∀ i, (q : PowerSeries K) * powerSeriesEuler K (f i) =
      ∑ j, (C i j : PowerSeries K) * f j) :
    (fun i => powerSeriesEuler K (f i)) = A *ᵥ f := by
  classical
  funext i
  apply mul_left_cancel₀ hq
  rw [hf]
  change (∑ j, (C i j : PowerSeries K) * f j) = (q : PowerSeries K) * ∑ j, A i j * f j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, hA]

theorem exists_linear_order_bound_of_regular_euler_matrix {σ K : Type*}
    [Fintype σ] [DecidableEq σ] [Field K] [CharZero K]
    (A : Matrix σ σ (PowerSeries K)) (q : Polynomial K) (C : Matrix σ σ (Polynomial K))
    (hq : (q : PowerSeries K) ≠ 0)
    (hA : ∀ i j, (q : PowerSeries K) * A i j = (C i j : PowerSeries K)) :
    ∃ B : ℕ, ∀ (f : σ → PowerSeries K) (D : ℕ) (P : σ → Polynomial K),
      (fun i => powerSeriesEuler K (f i)) = A *ᵥ f → 0 < D →
      (∀ i, (P i).natDegree < D) → (∑ i, (P i : PowerSeries K) * f i) ≠ 0 →
      (∑ i, (P i : PowerSeries K) * f i).order < (Fintype.card σ * D + B : ℕ) := by
  classical
  let m := Fintype.card σ
  let d := max q.natDegree (Finset.univ.sup (fun ij : σ × σ => (C ij.1 ij.2).natDegree))
  have hqd : q.natDegree ≤ d := le_max_left _ _
  have hCd (i j : σ) : (C i j).natDegree ≤ d :=
    (Finset.le_sup (f := fun ij : σ × σ => (C ij.1 ij.2).natDegree)
      (Finset.mem_univ (i, j))).trans (le_max_right _ _)
  obtain ⟨N, hN⟩ := exists_uniform_order_bound_stable_rows A
  refine ⟨m * m * d + N, ?_⟩
  intro f D P hf hD hP hF
  let F := ∑ i, (P i : PowerSeries K) * f i
  let φ := algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
  let v : ℕ → σ → FractionRing (PowerSeries K) :=
    fun n j => φ (polynomialEulerRows q C P n j : PowerSeries K)
  have hv : v 0 ≠ 0 := by
    intro hz
    apply hF
    apply Finset.sum_eq_zero
    intro j _
    have hj : φ (P j : PowerSeries K) = 0 := congrFun hz j
    have hpj : (P j : PowerSeries K) = 0 :=
      IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
        (hj.trans (map_zero φ).symm)
    rw [hpj, zero_mul]
  obtain ⟨r, hr, hrm, hTI, hdep⟩ :=
    exists_first_linear_dependence (K := FractionRing (PowerSeries K)) v hv
  have hrm' : r ≤ m := by simpa only [Module.finrank_fintype_fun_eq_card] using hrm
  let T : Matrix (Fin r) σ (Polynomial K) := fun i j => polynomialEulerRows q C P i.val j
  let Tₛ : Matrix (Fin r) σ (PowerSeries K) := T.map Polynomial.coeToPowerSeries.ringHom
  have hfq (i : σ) : (q : PowerSeries K) * powerSeriesEuler K (f i) =
      ∑ j, (C i j : PowerSeries K) * f j := by
    rw [congrFun hf i]
    change (q : PowerSeries K) * ∑ j, A i j * f j = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, hA]
  have hTfnz : Tₛ *ᵥ f ≠ 0 := by
    intro hz
    apply hF
    exact congrFun hz ⟨0, hr⟩
  have hlow (i : Fin r) : (F.order.toNat : ℕ∞) ≤ ((Tₛ *ᵥ f) i).order := by
    rw [PowerSeries.coe_toNat_order hF]
    exact order_le_polynomialEulerRows_sum_mul q C P f hfq i.val
  obtain ⟨J, hJ, hL⟩ := hN r Tₛ f F.order.toNat hTI
    (fun i => polynomialEulerRows_fraction_span_stable q C P A hq hA r hdep i) hf hTfnz hlow
  have hdeg (i : Fin r) (j : σ) : (T i j).natDegree ≤ D + m * d := by
    have hP' (j : σ) : (P j).natDegree ≤ D - 1 := by have := hP j; omega
    exact (polynomialEulerRows_natDegree_le q C P (D - 1) d hP' hqd hCd i.val j).trans
      (Nat.add_le_add (Nat.sub_lt hD Nat.zero_lt_one).le
        (Nat.mul_le_mul_right d (i.isLt.le.trans hrm')))
  have hdet := order_polynomial_minor_le T J (D + m * d) hdeg hJ
  rw [← PowerSeries.coe_toNat_order hJ] at hdet
  simp only [Fintype.card_fin] at hdet
  have hd : (Tₛ.submatrix id J).det.order.toNat ≤ r * (D + m * d) := by
    exact_mod_cast hdet
  have hbound : F.order.toNat < m * D + (m * m * d + N) := by
    calc
      _ < (Tₛ.submatrix id J).det.order.toNat + N := hL
      _ ≤ r * (D + m * d) + N := Nat.add_le_add_right hd N
      _ ≤ m * (D + m * d) + N := Nat.add_le_add_right (Nat.mul_le_mul_right _ hrm') N
      _ = _ := by ring
  rw [← PowerSeries.coe_toNat_order hF]
  exact_mod_cast hbound

theorem exists_linear_order_bound_of_cleared_euler_system {σ K : Type*}
    [Fintype σ] [DecidableEq σ] [Field K] [CharZero K]
    (q : Polynomial K) (C : Matrix σ σ (Polynomial K)) (hq : q.coeff 0 ≠ 0) :
    ∃ B : ℕ, ∀ (f : σ → PowerSeries K) (D : ℕ) (P : σ → Polynomial K),
      (∀ i, (q : PowerSeries K) * powerSeriesEuler K (f i) =
        ∑ j, (C i j : PowerSeries K) * f j) → 0 < D →
      (∀ i, (P i).natDegree < D) → (∑ i, (P i : PowerSeries K) * f i) ≠ 0 →
      (∑ i, (P i : PowerSeries K) * f i).order < (Fintype.card σ * D + B : ℕ) := by
  obtain ⟨A, hA⟩ := exists_powerSeries_matrix_of_polynomial_denominator q C hq
  have hq' : (q : PowerSeries K) ≠ 0 := by
    intro hz
    apply hq
    have h := congrArg (PowerSeries.coeff (R := K) 0) hz
    simpa only [Polynomial.coeff_coe, map_zero] using h
  obtain ⟨B, hB⟩ := exists_linear_order_bound_of_regular_euler_matrix A q C hq' hA
  refine ⟨B, ?_⟩
  intro f D P hf hD hP hF
  exact hB f D P (powerSeriesEuler_system_of_cleared q C A hq' hA f hf) hD hP hF

end DirichletL
