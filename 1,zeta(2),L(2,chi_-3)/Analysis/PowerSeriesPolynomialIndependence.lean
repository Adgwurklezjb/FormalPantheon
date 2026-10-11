import Comparator.Statement

/-!
Polynomial shifts for the auxiliary template in CDT v2,
supplied TeX 2910-2935 and 3965-3998.
-/

namespace DirichletL

open scoped Classical

theorem linearIndependent_shifted_powerSeries {K ι : Type*} [Field K] [Fintype ι]
    (f : ι → PowerSeries K)
    (hf : ∀ P : ι → Polynomial K, ∑ i, (P i : PowerSeries K) * f i = 0 → P = 0)
    (D : ℕ) : LinearIndependent K (fun p : ι × Fin D =>
      PowerSeries.monomial (R := K) p.2.val 1 * f p.1) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  let P : ι → Polynomial K := fun i => Polynomial.ofFn D (fun k => c (i, k))
  have hmono (i : ι) (k : Fin D) :
      (Polynomial.monomial k.val (c (i, k)) : PowerSeries K) =
        c (i, k) • PowerSeries.monomial (R := K) k.val 1 := by
    rw [Polynomial.coe_monomial]
    simpa only [smul_eq_mul, mul_one] using
      (PowerSeries.monomial (R := K) k.val).map_smul (c (i, k)) (1 : K)
  have hP : ∑ i, (P i : PowerSeries K) * f i = 0 := by
    calc
      _ = ∑ i, ∑ k : Fin D,
          c (i, k) • (PowerSeries.monomial (R := K) k.val 1 * f i) := by
        apply Finset.sum_congr rfl
        intro i hi
        change Polynomial.coeToPowerSeries.ringHom
          (Polynomial.ofFn D (fun k => c (i, k))) * f i = _
        rw [Polynomial.ofFn_eq_sum_monomial, map_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        change (Polynomial.monomial k.val (c (i, k)) : PowerSeries K) * f i = _
        rw [hmono, smul_mul_assoc]
      _ = ∑ p : ι × Fin D,
          c p • (PowerSeries.monomial (R := K) p.2.val 1 * f p.1) := by
        rw [Fintype.sum_prod_type]
      _ = 0 := hc
  have hPi : P p.1 = 0 := congrFun (hf P hP) p.1
  have hz : (fun k : Fin D => c (p.1, k)) = 0 :=
    Polynomial.injective_ofFn D (by simpa only [P, map_zero] using hPi)
  exact congrFun hz p.2

theorem linearIndependent_powerSeries_coefficients {K ι : Type*} [Field K] [Fintype ι]
    {f : ι → PowerSeries K} (hf : LinearIndependent K f) :
    LinearIndependent K (fun i => fun n : ℕ => PowerSeries.coeff (R := K) n (f i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  apply Fintype.linearIndependent_iff.mp hf c ?_ i
  apply PowerSeries.ext
  intro n
  have hn := congrFun hc n
  simpa only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply,
    Pi.zero_apply] using hn

end DirichletL
