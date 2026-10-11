import Analysis.GammaSeries
import Analysis.GammaLimit
import Analysis.DivisorSeries

/-!
Real coefficient-series identities and the radial limit for C in CDT v2,
Section 11.1, supplied `L2chi.tex` lines 7674-7680.
-/

open Filter Topology

namespace DirichletL

/-- The base gamma coefficients evaluate to their character-sum expression. -/
theorem hasSum_gammaBaseCoeff_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℕ => (gammaBaseCoeff m : ℝ) * q ^ m) (gammaLambertBase q) := by
  let f : ℕ → ℕ → ℝ := fun n k => chiMinusThree n / (k : ℝ) ^ 2 * q ^ (n * k)
  have hf : HasSum (fun p : ℕ × ℕ => f (p.1 + 1) (p.2 + 1))
      (gammaLambertBase q) := by
    rw [← tsum_gammaDoubleTerm hq hq1]
    exact (summable_gammaDoubleTerm hq hq1).hasSum
  have hs := hasSum_mul_divisors hf (by intro n; simp [f, chiMinusThree_zero])
    (by intro n; simp [f])
  convert hs using 1
  funext m
  rw [gammaBaseCoeff_cast_eq_divisorSum m, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  simp [f, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]

/-- The corrected gamma coefficient series evaluates to C. -/
theorem hasSum_gammaCoeff_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℕ => (gammaCoeff m : ℝ) * q ^ m) (gammaLambert q) := by
  have hsq : q ^ 2 < 1 := pow_lt_one₀ hq hq1 (by decide : 2 ≠ 0)
  let g : ℕ → ℝ := fun m => if Even m then
    (1 / 4 : ℝ) * (gammaBaseCoeff (m / 2) : ℝ) * q ^ m else 0
  have hinj : Function.Injective (fun n : ℕ => 2 * n) := by
    intro n k h
    change 2 * n = 2 * k at h
    omega
  have hc : HasSum g ((1 / 4 : ℝ) * gammaLambertBase (q ^ 2)) := by
    apply (hinj.hasSum_iff (f := g) ?_).mp
    · convert (hasSum_gammaBaseCoeff_mul_pow (sq_nonneg q) hsq).mul_left (1 / 4 : ℝ)
        using 1
      funext n
      simp [g, even_iff_two_dvd, pow_mul, mul_assoc]
    · intro m hm
      have hodd : ¬Even m := by
        rintro ⟨k, hk⟩
        exact hm ⟨k, by change 2 * k = m; omega⟩
      simp [g, hodd]
  have hs := (hasSum_gammaBaseCoeff_mul_pow hq hq1).sub hc
  convert hs using 1
  funext m
  by_cases hm : m = 0
  · simp [hm, gammaCoeff, gammaBaseCoeff_zero, g]
  · rw [gammaCoeff_cast_eq hm, sub_mul]
    simp only [g]
    split_ifs <;> simp

theorem summable_gammaCoeff_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun m : ℕ => (gammaCoeff m : ℝ) * q ^ m) :=
  (hasSum_gammaCoeff_mul_pow hq hq1).summable

theorem tsum_gammaCoeff_mul_pow {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) :
    (∑' m : ℕ, (gammaCoeff m : ℝ) * q ^ m) = gammaLambert q :=
  (hasSum_gammaCoeff_mul_pow hq hq1).tsum_eq

/-- The C coefficient series has the radial limit stated in CDT v2, Section 11.1. -/
theorem tendsto_tsum_gammaCoeff_mul_pow :
    Tendsto (fun q : ℝ => ∑' m : ℕ, (gammaCoeff m : ℝ) * q ^ m)
      (𝓝[Set.Ico (0 : ℝ) 1] 1) (𝓝 (zetaTwo / 4)) := by
  have hlim : Tendsto gammaLambert (𝓝[Set.Ico (0 : ℝ) 1] 1)
      (𝓝 (zetaTwo / 4)) :=
    tendsto_gammaLambert_one.mono_left (nhdsWithin_mono _ (by
      intro q hq
      exact ⟨hq.1, hq.2.le⟩))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact (tsum_gammaCoeff_mul_pow hq.1 hq.2).symm

end DirichletL
