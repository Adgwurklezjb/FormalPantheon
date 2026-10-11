import Analysis.QBinomialSeries

/-!
The Durfee-rectangle family in Lau-Lee-Ono v3, Lemma 4.1.3. A finite
telescoping proof makes this an input to the triple-product argument,
-/

namespace DirichletL

/-- The generating term for a Durfee rectangle with `k` rows and `k + l` columns. -/
noncomputable def qDurfeeTerm (d l k : ℕ) : PowerSeries ℤ :=
  (PowerSeries.X ^ d) ^ (k * (k + l)) * qPochhammerInvSeries d k *
    qPochhammerInvSeries d (k + l)

/-- The Durfee sum through rectangle index `N`, including index zero. -/
noncomputable def qDurfeePartial (d l N : ℕ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range (N + 1), qDurfeeTerm d l k

private noncomputable def qDurfeeBoundary (d l N : ℕ) : PowerSeries ℤ :=
  (PowerSeries.X ^ d) ^ ((N + 1) * (N + 1 + l)) * qPochhammerInvSeries d N *
    qPochhammerInvSeries d (N + 1 + l)

/-- The coefficientwise finite Durfee-rectangle series. -/
noncomputable def qDurfeeSeries (d l : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun m => PowerSeries.coeff (R := ℤ) m (qDurfeePartial d l m))

theorem coeff_qDurfeeSeries (d l m : ℕ) :
    PowerSeries.coeff (R := ℤ) m (qDurfeeSeries d l) =
      PowerSeries.coeff (R := ℤ) m (qDurfeePartial d l m) := by
  exact PowerSeries.coeff_mk _ _

theorem qDurfeePartial_succ (d l N : ℕ) :
    qDurfeePartial d l (N + 1) = qDurfeePartial d l N + qDurfeeTerm d l (N + 1) := by
  exact Finset.sum_range_succ _ _

private theorem qDurfeeTerm_step {d : ℕ} (hd : 0 < d) (l k : ℕ) :
    qDurfeeTerm d l (k + 1) - qDurfeeTerm d (l + 1) (k + 1) =
      qDurfeeBoundary d l k - qDurfeeBoundary d l (k + 1) := by
  let q : PowerSeries ℤ := PowerSeries.X ^ d
  have h (m : ℕ) :
      q ^ ((k + 1) * m) * qPochhammerInvSeries d (k + 1) * qPochhammerInvSeries d m -
        q ^ ((k + 1) * (m + 1)) * qPochhammerInvSeries d (k + 1) *
          qPochhammerInvSeries d (m + 1) =
      q ^ ((k + 1) * m) * qPochhammerInvSeries d k * qPochhammerInvSeries d m -
        q ^ ((k + 2) * (m + 1)) * qPochhammerInvSeries d (k + 1) *
          qPochhammerInvSeries d (m + 1) := by
    rw [← one_sub_mul_qPochhammerInvSeries_succ hd k,
      ← one_sub_mul_qPochhammerInvSeries_succ hd m]
    change q ^ ((k + 1) * m) * qPochhammerInvSeries d (k + 1) *
        ((1 - q ^ (m + 1)) * qPochhammerInvSeries d (m + 1)) -
        q ^ ((k + 1) * (m + 1)) * qPochhammerInvSeries d (k + 1) *
          qPochhammerInvSeries d (m + 1) = _
    simp only [Nat.mul_add, Nat.add_mul, one_mul, pow_add, pow_succ, pow_one, pow_two]
    ring
  simpa only [qDurfeeTerm, qDurfeeBoundary, q, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using h (k + 1 + l)

theorem qDurfeePartial_step {d : ℕ} (hd : 0 < d) (l N : ℕ) :
    qDurfeePartial d l N - qDurfeePartial d (l + 1) N =
      -((PowerSeries.X ^ d) ^ ((N + 1) * (N + 1 + l)) *
        qPochhammerInvSeries d N * qPochhammerInvSeries d (N + 1 + l)) := by
  change qDurfeePartial d l N - qDurfeePartial d (l + 1) N = -qDurfeeBoundary d l N
  induction N with
  | zero =>
    simp only [qDurfeePartial, Finset.sum_range_one, qDurfeeTerm, qDurfeeBoundary,
      zero_mul, pow_zero, qPochhammerInvSeries_zero, mul_one, one_mul, zero_add]
    rw [Nat.add_comm 1 l, ← one_sub_mul_qPochhammerInvSeries_succ hd l]
    ring
  | succ N ih =>
    calc
      _ = (qDurfeePartial d l N - qDurfeePartial d (l + 1) N) +
          (qDurfeeTerm d l (N + 1) - qDurfeeTerm d (l + 1) (N + 1)) := by
            rw [qDurfeePartial_succ, qDurfeePartial_succ]
            ring
      _ = -qDurfeeBoundary d l N +
          (qDurfeeBoundary d l N - qDurfeeBoundary d l (N + 1)) := by
            rw [ih, qDurfeeTerm_step hd]
      _ = _ := by ring

private theorem X_pow_dvd_qDurfeeBoundary {d : ℕ} (hd : 0 < d) (l N : ℕ) :
    (PowerSeries.X : PowerSeries ℤ) ^ (N + 1) ∣ qDurfeeBoundary d l N := by
  have h1 : N + 1 ≤ (N + 1) * (N + 1 + l) := by
    simpa only [mul_one] using Nat.mul_le_mul_left (N + 1) (show 1 ≤ N + 1 + l by omega)
  have h2 := Nat.mul_le_mul_right ((N + 1) * (N + 1 + l)) (show 1 ≤ d by omega)
  have he : N + 1 ≤ d * ((N + 1) * (N + 1 + l)) := by omega
  unfold qDurfeeBoundary
  rw [← pow_mul]
  exact dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (pow_dvd_pow PowerSeries.X he) _) _

theorem qDurfeeSeries_succ {d : ℕ} (hd : 0 < d) (l : ℕ) :
    qDurfeeSeries d l = qDurfeeSeries d (l + 1) := by
  apply PowerSeries.ext
  intro m
  rw [coeff_qDurfeeSeries, coeff_qDurfeeSeries]
  apply sub_eq_zero.mp
  rw [← map_sub, qDurfeePartial_step hd]
  change PowerSeries.coeff (R := ℤ) m (-qDurfeeBoundary d l m) = 0
  rw [map_neg, PowerSeries.X_pow_dvd_iff.mp (X_pow_dvd_qDurfeeBoundary hd l m) m
    (Nat.lt_succ_self m), neg_zero]

theorem qDurfeeSeries_eq_zero_index {d : ℕ} (hd : 0 < d) (l : ℕ) :
    qDurfeeSeries d l = qDurfeeSeries d 0 := by
  induction l with
  | zero => rfl
  | succ l ih => exact (qDurfeeSeries_succ hd l).symm.trans ih

/-- The Durfee-rectangle family equals the exact inverse Euler product. -/
theorem qDurfeeSeries_eq_formalProduct_inv {d : ℕ} (hd : 0 < d) (l : ℕ) :
    qDurfeeSeries d l = formalProduct (fun i => oneSubInv (d * (i + 1))) := by
  apply PowerSeries.ext
  intro m
  rw [coeff_formalProduct]
  change PowerSeries.coeff (R := ℤ) m (qDurfeeSeries d l) =
    PowerSeries.coeff (R := ℤ) m (qPochhammerInvSeries d (m + 1))
  calc
    _ = PowerSeries.coeff (R := ℤ) m (qDurfeeSeries d (m + 1)) := by
      rw [qDurfeeSeries_eq_zero_index hd l, qDurfeeSeries_eq_zero_index hd (m + 1)]
    _ = _ := by
      rw [coeff_qDurfeeSeries, qDurfeePartial, map_sum, Finset.sum_eq_single 0]
      · simp [qDurfeeTerm]
      · intro k _ hk
        have h2 := Nat.mul_le_mul_right (k + (m + 1)) (show 1 ≤ k by omega)
        have h3 := Nat.mul_le_mul_right (k * (k + (m + 1))) (show 1 ≤ d by omega)
        have he : m + 1 ≤ d * (k * (k + (m + 1))) := by omega
        have hx : (PowerSeries.X : PowerSeries ℤ) ^ (m + 1) ∣ qDurfeeTerm d (m + 1) k := by
          unfold qDurfeeTerm
          rw [← pow_mul]
          exact dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_left (pow_dvd_pow PowerSeries.X he) _) _
        exact PowerSeries.X_pow_dvd_iff.mp hx m (Nat.lt_succ_self m)
      · simp

end DirichletL
