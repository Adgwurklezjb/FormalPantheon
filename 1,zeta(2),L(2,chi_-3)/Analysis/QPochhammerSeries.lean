import Analysis.QBinomialSeries

/-!
Euler's q-Pochhammer expansion as an exact identity in integer formal power
series. See Lau-Lee-Ono v3, Section 3.5.4. This is an input to the Jacobi
triple-product bridge for the eta products in CDT v2 Section 11.1.
-/

namespace DirichletL

theorem coeff_qPochhammer_eq_sum {d m N : ℕ} {a : PowerSeries ℤ}
    (hd : 0 < d) (hmN : m < N) :
    PowerSeries.coeff (R := ℤ) m (qPochhammer a (PowerSeries.X ^ d) N) =
      ∑ k ∈ Finset.range (m + 2), PowerSeries.coeff (R := ℤ) m
        (qPochhammerInvSeries d k * (-a) ^ k * (PowerSeries.X ^ d) ^ k.choose 2) := by
  have hcoeff (k : ℕ) (hk : k ≤ N) :
      PowerSeries.coeff (R := ℤ) m
          (qBinomial (PowerSeries.X ^ d) N k * (-a) ^ k *
            (PowerSeries.X ^ d) ^ k.choose 2) =
        PowerSeries.coeff (R := ℤ) m
          (qPochhammerInvSeries d k * (-a) ^ k *
            (PowerSeries.X ^ d) ^ k.choose 2) := by
    have h : (PowerSeries.X : PowerSeries ℤ) ^ N ∣
        (qBinomial (PowerSeries.X ^ d) N k - qPochhammerInvSeries d k) *
          (-a) ^ k * (PowerSeries.X ^ d) ^ k.choose 2 := by
      convert dvd_mul_of_dvd_left (X_pow_dvd_qBinomial_mul_triangular_sub hd hk)
        ((-a) ^ k) using 1
      ring
    have hz := PowerSeries.X_pow_dvd_iff.mp h m hmN
    simpa only [sub_mul, map_sub, sub_eq_zero] using hz
  rw [qPochhammer_eq_sum_qBinomial, map_sum]
  calc
    _ = ∑ k ∈ Finset.range (N + 1), PowerSeries.coeff (R := ℤ) m
        (qPochhammerInvSeries d k * (-a) ^ k * (PowerSeries.X ^ d) ^ k.choose 2) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hcoeff k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega : m + 2 ≤ N + 1))
      intro k _ hkm
      have hmk : m < d * k.choose 2 := by
        have h1 := le_choose_two_add_one k
        have h2 := Nat.mul_le_mul_right (k.choose 2) (show 1 ≤ d by omega)
        simp only [Finset.mem_range] at hkm
        omega
      have hq : (PowerSeries.X : PowerSeries ℤ) ^ (d * k.choose 2) ∣
          (PowerSeries.X ^ d) ^ k.choose 2 := by rw [← pow_mul]
      have hp := dvd_mul_of_dvd_right hq (qPochhammerInvSeries d k * (-a) ^ k)
      exact PowerSeries.X_pow_dvd_iff.mp hp m hmk

/-- Euler's expansion, with each coefficient expressed as an explicitly finite sum. -/
theorem formalProduct_qPochhammer_eq_sum {d : ℕ} {a : PowerSeries ℤ}
    (hd : 0 < d) :
    formalProduct (fun i => 1 - a * (PowerSeries.X ^ d) ^ i) =
      PowerSeries.mk (fun m => ∑ k ∈ Finset.range (m + 2), PowerSeries.coeff (R := ℤ) m
        (qPochhammerInvSeries d k * (-a) ^ k * (PowerSeries.X ^ d) ^ k.choose 2)) := by
  apply PowerSeries.ext
  intro m
  rw [coeff_formalProduct, PowerSeries.coeff_mk]
  exact coeff_qPochhammer_eq_sum hd (Nat.lt_succ_self m)

end DirichletL
