import Arithmetic.Denominators
import Analysis.BetaDoubleSeries
import Analysis.DivisorSeries

/-!
The real coefficient-series identity for B in CDT v2, Section 11.1,
supplied `L2chi.tex` line 7673, on the interval `0 <= q < 1`.
-/

open Filter Topology

namespace DirichletL

/-- The checked beta coefficient series sums to the Lambert expression. -/
theorem hasSum_betaCoeff_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℕ => (betaCoeff m : ℝ) * q ^ m) (betaLambert q) := by
  let f : ℕ → ℕ → ℝ := fun n k => if k = 0 then 0 else
    chiMinusThree n / (n : ℝ) ^ 2 * (-1 : ℝ) ^ (k - 1) * q ^ (n * k)
  have hf : HasSum (fun p : ℕ × ℕ => f (p.1 + 1) (p.2 + 1)) (betaLambert q) := by
    rw [← tsum_betaDoubleTerm hq hq1]
    convert (summable_betaDoubleTerm hq hq1).hasSum using 1
  have hs := hasSum_mul_divisors hf (by intro n; simp [f, chiMinusThree_zero])
    (by intro n; simp [f])
  convert hs using 1
  funext m
  by_cases hm : m = 0
  · simp [hm, betaCoeff_zero]
  · rw [betaCoeff_cast_eq_divisorSum hm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have hdiv : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hquot : 0 < m / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdiv)
      (Nat.pos_of_mem_divisors hd)
    simp [f, Nat.ne_of_gt hquot, Nat.mul_div_cancel' hdiv]

theorem summable_betaCoeff_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℕ => (betaCoeff m : ℝ) * q ^ m) :=
  (hasSum_betaCoeff_mul_pow hq hq1).summable

theorem tsum_betaCoeff_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑' m : ℕ, (betaCoeff m : ℝ) * q ^ m) = betaLambert q :=
  (hasSum_betaCoeff_mul_pow hq hq1).tsum_eq

/-- The coefficient series has the same radial limit as B in CDT v2, Section 11.1. -/
theorem tendsto_tsum_betaCoeff_mul_pow :
    Tendsto (fun q : ℝ => ∑' m : ℕ, (betaCoeff m : ℝ) * q ^ m)
      (𝓝[Set.Ico (0 : ℝ) 1] 1) (𝓝 (lTwoChiMinusThree / 2)) := by
  have hlim : Tendsto betaLambert (𝓝[Set.Ico (0 : ℝ) 1] 1)
      (𝓝 (lTwoChiMinusThree / 2)) :=
    tendsto_betaLambert_one.mono_left (nhdsWithin_mono _ (by
      intro q hq
      exact ⟨hq.1, hq.2.le⟩))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (tsum_betaCoeff_mul_pow hq.1 hq.2).symm

end DirichletL
