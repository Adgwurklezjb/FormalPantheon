import Analysis.PolynomialEulerRows
import Analysis.PowerSeriesMatrixEuler
import Analysis.PowerSeriesOrderBounds

/-!
The derivative rows applied to a formal solution in the specialization of
CDT v2 `lem_Shidlovsky`, supplied TeX 2910-2935. Meanings and edge checks
-/

namespace DirichletL

open scoped Matrix

theorem mul_powerSeriesEuler_pow {R : Type*} [CommRing R] (q : PowerSeries R) (n : ℕ) :
    q * powerSeriesEuler R (q ^ n) =
      (n : PowerSeries R) * q ^ n * powerSeriesEuler R q := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Derivation.leibniz_pow]
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, pow_succ]
    ring

theorem polynomialEulerRows_sum_mul_succ {σ R : Type*} [Fintype σ] [CommRing R]
    (q : Polynomial R) (C : Matrix σ σ (Polynomial R)) (P : σ → Polynomial R)
    (f : σ → PowerSeries R)
    (hf : ∀ i, (q : PowerSeries R) * powerSeriesEuler R (f i) =
      ∑ j, (C i j : PowerSeries R) * f j) (n : ℕ) :
    ∑ j, (polynomialEulerRows q C P (n + 1) j : PowerSeries R) * f j =
      (q : PowerSeries R) * powerSeriesEuler R
        (∑ j, (polynomialEulerRows q C P n j : PowerSeries R) * f j) -
      (n : PowerSeries R) * powerSeriesEuler R (q : PowerSeries R) *
        ∑ j, (polynomialEulerRows q C P n j : PowerSeries R) * f j := by
  classical
  let T : σ → PowerSeries R := fun j => polynomialEulerRows q C P n j
  let Cₛ : Matrix σ σ (PowerSeries R) := C.map Polynomial.coeToPowerSeries.ringHom
  have hrow (j : σ) : (polynomialEulerRows q C P (n + 1) j : PowerSeries R) =
      (q : PowerSeries R) * powerSeriesEuler R (T j) + (T ᵥ* Cₛ) j -
        (n : PowerSeries R) * powerSeriesEuler R (q : PowerSeries R) * T j := by
    change Polynomial.coeToPowerSeries.ringHom (polynomialEulerRows q C P (n + 1) j) = _
    simp only [polynomialEulerRows_succ, map_sub, map_add, map_mul, map_natCast,
      RingHom.map_vecMul, Polynomial.coeToPowerSeries.ringHom_apply, coe_polynomialEuler]
    rfl
  have hd : powerSeriesEuler R (∑ j, T j * f j) =
      (∑ j, powerSeriesEuler R (T j) * f j) + ∑ j, T j * powerSeriesEuler R (f j) := by
    exact congrFun (powerSeriesEuler_matrix_mulVec (fun (_ : Fin 1) j => T j) f) 0
  have hc : ∑ j, (T ᵥ* Cₛ) j * f j =
      (q : PowerSeries R) * ∑ j, T j * powerSeriesEuler R (f j) := by
    change (T ᵥ* Cₛ) ⬝ᵥ f = _
    rw [← Matrix.dotProduct_mulVec]
    have hCf : Cₛ *ᵥ f = fun i => (q : PowerSeries R) * powerSeriesEuler R (f i) :=
      funext (fun i => (hf i).symm)
    rw [hCf]
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change ∑ j, (polynomialEulerRows q C P (n + 1) j : PowerSeries R) * f j =
    (q : PowerSeries R) * powerSeriesEuler R (∑ j, T j * f j) -
      (n : PowerSeries R) * powerSeriesEuler R (q : PowerSeries R) * ∑ j, T j * f j
  simp_rw [hrow]
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc, ← Finset.mul_sum]
  rw [hc, hd]
  ring

theorem polynomialEulerRows_sum_mul {σ R : Type*} [Fintype σ] [CommRing R]
    (q : Polynomial R) (C : Matrix σ σ (Polynomial R)) (P : σ → Polynomial R)
    (f : σ → PowerSeries R)
    (hf : ∀ i, (q : PowerSeries R) * powerSeriesEuler R (f i) =
      ∑ j, (C i j : PowerSeries R) * f j) (n : ℕ) :
    ∑ j, (polynomialEulerRows q C P n j : PowerSeries R) * f j =
      (q : PowerSeries R) ^ n *
        ((powerSeriesEuler R : PowerSeries R → PowerSeries R)^[n]
          (∑ j, (P j : PowerSeries R) * f j)) := by
  induction n with
  | zero => simp only [polynomialEulerRows_zero, pow_zero, Function.iterate_zero_apply, one_mul]
  | succ n ih =>
    rw [polynomialEulerRows_sum_mul_succ q C P f hf, ih,
      Function.iterate_succ_apply', Derivation.leibniz]
    simp only [smul_eq_mul]
    have h := mul_powerSeriesEuler_pow (q : PowerSeries R) n
    rw [pow_succ]
    linear_combination
      ((powerSeriesEuler R : PowerSeries R → PowerSeries R)^[n]
        (∑ j, (P j : PowerSeries R) * f j)) * h

theorem order_le_polynomialEulerRows_sum_mul {σ K : Type*} [Fintype σ] [Field K]
    (q : Polynomial K) (C : Matrix σ σ (Polynomial K)) (P : σ → Polynomial K)
    (f : σ → PowerSeries K)
    (hf : ∀ i, (q : PowerSeries K) * powerSeriesEuler K (f i) =
      ∑ j, (C i j : PowerSeries K) * f j) (n : ℕ) :
    (∑ j, (P j : PowerSeries K) * f j).order ≤
      (∑ j, (polynomialEulerRows q C P n j : PowerSeries K) * f j).order := by
  rw [polynomialEulerRows_sum_mul q C P f hf, PowerSeries.order_mul]
  exact (order_le_iterate_powerSeriesEuler _ n).trans (le_add_of_nonneg_left bot_le)

end DirichletL
