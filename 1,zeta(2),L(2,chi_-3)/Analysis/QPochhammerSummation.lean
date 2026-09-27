import Analysis.FormalSeriesAlgebra
import Analysis.QPochhammerSeries
import Analysis.DurfeeSeries

/-!
Summation interfaces for the exact Euler and Durfee identities in
Lau-Lee-Ono v3, Sections 3.5.4 and 4.1.3. The topology is Mathlib's
coefficientwise topology on integer power series.
-/

namespace DirichletL

open scoped PowerSeries.WithPiTopology

/-- The k-th term in Euler's q-Pochhammer expansion. -/
noncomputable def qEulerTerm (a : PowerSeries ℤ) (d k : ℕ) : PowerSeries ℤ :=
  qPochhammerInvSeries d k * (-a) ^ k * (PowerSeries.X ^ d) ^ k.choose 2

theorem X_pow_dvd_qEulerTerm (a : PowerSeries ℤ) (d k : ℕ) :
    (PowerSeries.X : PowerSeries ℤ) ^ (d * k.choose 2) ∣ qEulerTerm a d k := by
  unfold qEulerTerm
  rw [← pow_mul]
  exact dvd_mul_left _ _

theorem hasSum_qEulerTerm {d : ℕ} {a : PowerSeries ℤ} (hd : 0 < d) :
    HasSum (qEulerTerm a d) (formalProduct (fun i => 1 - a * (PowerSeries.X ^ d) ^ i)) := by
  rw [formalProduct_qPochhammer_eq_sum hd]
  apply hasSum_powerSeries_of_finite_coeff (qEulerTerm a d) (fun m => Finset.range (m + 2))
  intro m k hk
  have hmk : m < d * k.choose 2 := by
    have h1 := le_choose_two_add_one k
    have h2 := Nat.mul_le_mul_right (k.choose 2) (show 1 ≤ d by omega)
    simp only [Finset.mem_range] at hk
    omega
  exact PowerSeries.X_pow_dvd_iff.mp (X_pow_dvd_qEulerTerm a d k) m hmk

theorem hasSum_qDurfeeTerm {d : ℕ} (hd : 0 < d) (l : ℕ) :
    HasSum (qDurfeeTerm d l) (formalProduct (fun i => oneSubInv (d * (i + 1)))) := by
  have hf (k : ℕ) : (PowerSeries.X : PowerSeries ℤ) ^ k ∣ qDurfeeTerm d l k := by
    by_cases hk : k = 0
    · subst k
      simp
    have h1 : k ≤ k * (k + l) := by
      simpa only [mul_one] using Nat.mul_le_mul_left k (show 1 ≤ k + l by omega)
    have h2 := Nat.mul_le_mul_right (k * (k + l)) (show 1 ≤ d by omega)
    have he : k ≤ d * (k * (k + l)) := by omega
    unfold qDurfeeTerm
    rw [← pow_mul]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_left (pow_dvd_pow PowerSeries.X he) _) _
  rw [← qDurfeeSeries_eq_formalProduct_inv hd l]
  simpa only [qDurfeeSeries, qDurfeePartial, map_sum] using
    hasSum_powerSeries_of_X_pow_dvd hf

theorem formalProduct_qPochhammer_mul_inv {d : ℕ} (hd : 0 < d) :
    formalProduct (fun i => 1 - (PowerSeries.X ^ d) ^ (i + 1)) *
      formalProduct (fun i => oneSubInv (d * (i + 1))) = (1 : PowerSeries ℤ) := by
  have hle (i : ℕ) : i + 1 ≤ d * (i + 1) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (i + 1) (show 1 ≤ d by omega)
  have hf (i : ℕ) : (PowerSeries.X : PowerSeries ℤ) ^ (i + 1) ∣
      (1 - (PowerSeries.X ^ d) ^ (i + 1)) - 1 := by
    rw [← pow_mul]
    exact dvd_X_pow_sub_one_sub (hle i)
  have hg (i : ℕ) : (PowerSeries.X : PowerSeries ℤ) ^ (i + 1) ∣
      oneSubInv (d * (i + 1)) - 1 :=
    dvd_oneSubInv_sub_one (Nat.mul_pos hd (Nat.succ_pos i)) (hle i)
  rw [formalProduct_mul hf hg]
  calc
    _ = formalProduct (fun _ => (1 : PowerSeries ℤ)) := by
      apply congrArg formalProduct
      funext i
      rw [← pow_mul]
      exact oneSubInv_rightInv (Nat.mul_pos hd (Nat.succ_pos i))
    _ = 1 := formalProduct_one

end DirichletL
