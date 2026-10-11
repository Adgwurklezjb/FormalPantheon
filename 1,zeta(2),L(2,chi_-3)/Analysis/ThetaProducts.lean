import Analysis.ThetaSeries
import Analysis.JacobiTripleProduct

/-!
The three formal theta products obtained from Lau-Lee-Ono v3, Theorem 4.1.4.
These supply the theta/product identities for CDT v2 Section 11.1.
Complex analytic evaluation is a separate obligation.
-/

namespace DirichletL

open scoped PowerSeries.WithPiTopology

private theorem choose_two_square (n : ℕ) : n + 2 * n.choose 2 = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (n + 1).choose 2 = n + n.choose 2 := by
      simpa using Nat.choose_succ_succ n 1
    rw [h]
    nlinarith

private theorem choose_two_pronic (n : ℕ) : 2 * (n + 1).choose 2 = n * (n + 1) := by
  have h := choose_two_square (n + 1)
  nlinarith

private theorem two_mul_add_choose_two (n : ℕ) : 2 * n + 2 * n.choose 2 = n * (n + 1) := by
  have h := choose_two_square n
  nlinarith

private theorem tsum_tail_of_hasSum {f : ℕ → PowerSeries ℤ} {s : PowerSeries ℤ}
    (h : HasSum f s) : (∑' n, f (n + 1)) = s - f 0 := by
  simpa using ((hasSum_nat_add_iff' 1).mpr h).tsum_eq

/-- The square theta product; the two equal odd plus products form a square. -/
theorem thetaThreeSeries_eq_formalProduct :
    thetaThreeSeries =
      formalProduct (fun i => 1 - PowerSeries.X ^ (2 * (i + 1))) *
        formalProduct (fun i => 1 + PowerSeries.X ^ (2 * i + 1)) ^ 2 := by
  have h := jacobiTripleProduct (d := 2) (a := -PowerSeries.X) (b := -PowerSeries.X)
    (by omega) (by ring)
  simp only [neg_neg, neg_mul, sub_neg_eq_add, ← pow_mul, ← pow_succ',
    ← pow_add, choose_two_square] at h
  rw [pow_two, ← mul_assoc, h, hasSum_X_pow_square.tsum_eq,
    tsum_tail_of_hasSum hasSum_X_pow_square]
  simp only [zero_pow two_ne_zero, pow_zero, thetaThreeSeries]
  ring

/-- The alternating square theta product. -/
theorem thetaFourSeries_eq_formalProduct :
    thetaFourSeries =
      formalProduct (fun i => 1 - PowerSeries.X ^ (2 * (i + 1))) *
        formalProduct (fun i => 1 - PowerSeries.X ^ (2 * i + 1)) ^ 2 := by
  have h := jacobiTripleProduct (d := 2) (a := PowerSeries.X) (b := PowerSeries.X)
    (by omega) (by ring)
  have ht (n : ℕ) : (-PowerSeries.X : PowerSeries ℤ) ^ n *
      (PowerSeries.X ^ 2) ^ n.choose 2 = (-1) ^ n * PowerSeries.X ^ (n ^ 2) := by
    rw [neg_pow, ← pow_mul, mul_assoc, ← pow_add, choose_two_square]
  simp only [ht] at h
  simp only [← pow_mul, ← pow_succ'] at h
  rw [pow_two, ← mul_assoc, h, hasSum_neg_one_pow_mul_X_square.tsum_eq,
    tsum_tail_of_hasSum hasSum_neg_one_pow_mul_X_square]
  simp only [zero_pow two_ne_zero, pow_zero, one_mul, thetaFourSeries]
  ring

/-- The normalized second theta product retains its initial constant factor 2. -/
theorem thetaTwoNormalizedSeries_eq_formalProduct :
    thetaTwoNormalizedSeries =
      formalProduct (fun i => 1 - PowerSeries.X ^ (2 * (i + 1))) *
        formalProduct (fun i => 1 + PowerSeries.X ^ (2 * i)) *
        formalProduct (fun i => 1 + PowerSeries.X ^ (2 * (i + 1))) := by
  have h := jacobiTripleProduct (d := 2) (a := -1) (b := -(PowerSeries.X ^ 2))
    (by omega) (by ring)
  have he (n : ℕ) : 2 + 2 * n = 2 * (n + 1) := by omega
  simp only [neg_neg, neg_mul, one_mul, sub_neg_eq_add, one_pow, ← pow_mul,
    ← pow_add, two_mul_add_choose_two, he] at h
  have hfirst : HasSum (fun n : ℕ => (PowerSeries.X : PowerSeries ℤ) ^ (2 * n.choose 2))
      (sparsePowerSeries natPronicEmbedding (fun _ => 1) + 1) := by
    have ht : HasSum (fun n : ℕ => (PowerSeries.X : PowerSeries ℤ) ^
        (2 * (n + 1).choose 2)) (sparsePowerSeries natPronicEmbedding (fun _ => 1)) := by
      simpa only [choose_two_pronic] using hasSum_X_pow_pronic
    simpa using (hasSum_nat_add_iff (f := fun n : ℕ =>
      (PowerSeries.X : PowerSeries ℤ) ^ (2 * n.choose 2)) 1).mp ht
  rw [h, hfirst.tsum_eq, tsum_tail_of_hasSum hasSum_X_pow_pronic]
  simp only [zero_mul, pow_zero, thetaTwoNormalizedSeries]
  ring

end DirichletL
