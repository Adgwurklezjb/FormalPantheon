import Arithmetic.QBinomial
import Analysis.Hauptmodul

/-!
Exact coefficient stabilization of Gaussian binomials. This supplies the
formal limit in Lau-Lee-Ono v3, Section 3.5.4, for the theta/product bridge
in CDT v2 Section 11.1. All inverse factors are units in the integer
power-series ring; no analytic limit or numerical approximation is used.
-/

namespace DirichletL

/-- The inverse of `(X^d; X^d)_n`, using the existing exact unit inverses. -/
noncomputable def qPochhammerInvSeries (d n : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range n, oneSubInv (d * (i + 1))

@[simp] theorem qPochhammerInvSeries_zero (d : ℕ) : qPochhammerInvSeries d 0 = 1 := by
  simp [qPochhammerInvSeries]

theorem qPochhammerInvSeries_succ (d n : ℕ) :
    qPochhammerInvSeries d (n + 1) =
      qPochhammerInvSeries d n * oneSubInv (d * (n + 1)) := by
  exact Finset.prod_range_succ _ _

theorem one_sub_mul_qPochhammerInvSeries_succ {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (1 - (PowerSeries.X ^ d) ^ (n + 1)) * qPochhammerInvSeries d (n + 1) =
      qPochhammerInvSeries d n := by
  rw [qPochhammerInvSeries_succ, ← pow_mul]
  calc
    _ = qPochhammerInvSeries d n *
        ((1 - PowerSeries.X ^ (d * (n + 1))) * oneSubInv (d * (n + 1))) := by ring
    _ = _ := by rw [oneSubInv_rightInv (Nat.mul_pos hd (Nat.succ_pos n)), mul_one]

theorem qPochhammer_X_mul_invSeries {d : ℕ} (hd : 0 < d) (n : ℕ) :
    qPochhammer (PowerSeries.X ^ d) (PowerSeries.X ^ d) n *
      qPochhammerInvSeries d n = (1 : PowerSeries ℤ) := by
  unfold qPochhammer qPochhammerInvSeries
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rw [← pow_succ', ← pow_mul]
  exact oneSubInv_rightInv (Nat.mul_pos hd (Nat.succ_pos i))

theorem qBinomial_X_eq_qPochhammer_mul_inv {d N k : ℕ} (hd : 0 < d) (hk : k ≤ N) :
    qBinomial (PowerSeries.X ^ d) N k =
      qPochhammer ((PowerSeries.X ^ d) ^ (N - k + 1)) (PowerSeries.X ^ d) k *
        qPochhammerInvSeries d k := by
  let q : PowerSeries ℤ := PowerSeries.X ^ d
  have hkInv : qPochhammer q q k * qPochhammerInvSeries d k = 1 :=
    qPochhammer_X_mul_invSeries hd k
  have hmInv : qPochhammer q q (N - k) * qPochhammerInvSeries d (N - k) = 1 :=
    qPochhammer_X_mul_invSeries hd (N - k)
  have hsplit : qPochhammer q q N =
      qPochhammer q q (N - k) * qPochhammer (q ^ (N - k + 1)) q k := by
    calc
      _ = qPochhammer q q ((N - k) + k) := by rw [Nat.sub_add_cancel hk]
      _ = _ := by rw [qPochhammer_add, ← pow_succ']
  change qBinomial q N k = _
  calc
    _ = (qBinomial q N k * qPochhammer q q k * qPochhammer q q (N - k)) *
        qPochhammerInvSeries d (N - k) * qPochhammerInvSeries d k := by
          calc
            _ = qBinomial q N k * (qPochhammer q q k * qPochhammerInvSeries d k) *
                (qPochhammer q q (N - k) * qPochhammerInvSeries d (N - k)) := by
                  rw [hkInv, hmInv, mul_one, mul_one]
            _ = _ := by ring
    _ = qPochhammer q q N * qPochhammerInvSeries d (N - k) *
        qPochhammerInvSeries d k := by rw [qBinomial_mul_qPochhammer q hk]
    _ = qPochhammer (q ^ (N - k + 1)) q k * qPochhammerInvSeries d k := by
      rw [hsplit]
      calc
        _ = (qPochhammer q q (N - k) * qPochhammerInvSeries d (N - k)) *
            (qPochhammer (q ^ (N - k + 1)) q k * qPochhammerInvSeries d k) := by ring
        _ = _ := by rw [hmInv, one_mul]

theorem X_pow_dvd_qBinomial_X_sub_inv {d N k : ℕ} (hd : 0 < d) (hk : k ≤ N) :
    (PowerSeries.X : PowerSeries ℤ) ^ (d * (N - k + 1)) ∣
      qBinomial (PowerSeries.X ^ d) N k - qPochhammerInvSeries d k := by
  rw [qBinomial_X_eq_qPochhammer_mul_inv hd hk]
  have ha : (PowerSeries.X : PowerSeries ℤ) ^ (d * (N - k + 1)) ∣
      (PowerSeries.X ^ d) ^ (N - k + 1) := by rw [← pow_mul]
  have h := dvd_qPochhammer_sub_one (q := PowerSeries.X ^ d) ha k
  simpa only [sub_mul, one_mul] using dvd_mul_of_dvd_left h (qPochhammerInvSeries d k)

theorem coeff_qBinomial_X_eq_inv {d N k m : ℕ} (hd : 0 < d) (hk : k ≤ N)
    (hm : m < d * (N - k + 1)) :
    PowerSeries.coeff (R := ℤ) m (qBinomial (PowerSeries.X ^ d) N k) =
      PowerSeries.coeff (R := ℤ) m (qPochhammerInvSeries d k) := by
  have h := PowerSeries.X_pow_dvd_iff.mp (X_pow_dvd_qBinomial_X_sub_inv hd hk) m hm
  simpa only [map_sub, sub_eq_zero] using h

theorem X_pow_dvd_qBinomial_mul_triangular_sub {d N k : ℕ}
    (hd : 0 < d) (hk : k ≤ N) :
    (PowerSeries.X : PowerSeries ℤ) ^ N ∣
      (qBinomial (PowerSeries.X ^ d) N k - qPochhammerInvSeries d k) *
        (PowerSeries.X ^ d) ^ k.choose 2 := by
  have hq : (PowerSeries.X : PowerSeries ℤ) ^ (d * k.choose 2) ∣
      (PowerSeries.X ^ d) ^ k.choose 2 := by rw [← pow_mul]
  have hp : (PowerSeries.X : PowerSeries ℤ) ^ (d * (N - k + 1) + d * k.choose 2) ∣
      (qBinomial (PowerSeries.X ^ d) N k - qPochhammerInvSeries d k) *
        (PowerSeries.X ^ d) ^ k.choose 2 := by
    simpa only [pow_add] using
      mul_dvd_mul (X_pow_dvd_qBinomial_X_sub_inv hd hk) hq
  have hle : N ≤ d * (N - k + 1) + d * k.choose 2 := by
    have h1 := Nat.mul_le_mul_right (N - k + 1) (show 1 ≤ d by omega)
    have h2 := Nat.mul_le_mul_right (k.choose 2) (show 1 ≤ d by omega)
    have h3 := le_choose_two_add_one k
    omega
  exact dvd_trans (pow_dvd_pow PowerSeries.X hle) hp

end DirichletL
