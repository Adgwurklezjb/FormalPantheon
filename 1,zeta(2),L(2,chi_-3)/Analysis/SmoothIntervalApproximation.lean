import Mathlib

/-!
Smooth interval comparisons for the Wiener-Ikehara route to CDT v2,
Section 2.2 (supplied TeX 3291-3310). The comparison argument appears
in the PrimeNumberTheoremAnd contributors' Wiener.lean at revision
0766218b21b11ddf24103352ece7f0cb730945e0, lines 1824-1878, archived
The cutoffs here are Mathlib's native ContDiffBump functions.
-/

namespace DirichletL

open MeasureTheory Set
open scoped ContDiff

theorem exists_contDiff_le_indicator_Ico {a b ε : ℝ} (ha : 0 < a)
    (hε : 0 < ε) (hε' : ε < b - a) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioi 0 ∧
      0 ≤ ψ ∧ ψ ≤ (Ico a b).indicator 1 ∧ b - a - ε ≤ ∫ y in Ioi (0 : ℝ), ψ y := by
  let χ : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a - ε) / 2, (b - a) / 2, by linarith, by linarith⟩
  have hts : tsupport (χ : ℝ → ℝ) = Icc a b := by
    rw [χ.tsupport_eq, Real.closedBall_eq_Icc]
    change Icc ((a + b) / 2 - (b - a) / 2) ((a + b) / 2 + (b - a) / 2) = _
    ring_nf
  have hsp : Function.support (χ : ℝ → ℝ) = Ioo a b := by
    rw [χ.support_eq, Real.ball_eq_Ioo]
    change Ioo ((a + b) / 2 - (b - a) / 2) ((a + b) / 2 + (b - a) / 2) = _
    ring_nf
  have hlow : (Icc (a + ε / 2) (b - ε / 2)).indicator (1 : ℝ → ℝ) ≤ χ := by
    intro y
    by_cases hy : y ∈ Icc (a + ε / 2) (b - ε / 2)
    · have hy' : y ∈ Metric.closedBall ((a + b) / 2) χ.rIn := by
        rw [Real.closedBall_eq_Icc]
        change (a + b) / 2 - (b - a - ε) / 2 ≤ y ∧
          y ≤ (a + b) / 2 + (b - a - ε) / 2
        constructor <;> linarith [hy.1, hy.2]
      simp only [indicator_of_mem hy, Pi.one_apply, χ.one_of_mem_closedBall hy', le_refl]
    · simpa only [indicator_of_not_mem hy] using χ.nonneg (x := y)
  have hupp : (χ : ℝ → ℝ) ≤ (Ico a b).indicator 1 := by
    intro y
    by_cases hy : y ∈ Ico a b
    · simpa only [indicator_of_mem hy, Pi.one_apply] using χ.le_one (x := y)
    · have hz : χ y = 0 := by
        by_contra hn
        have hy' : y ∈ Ioo a b := hsp ▸ hn
        exact hy (Ioo_subset_Ico_self hy')
      simp only [hz, indicator_of_not_mem hy, le_refl]
  have hJ : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le (by linarith) hy.1
  have hint : (∫ y in Ioi (0 : ℝ),
      (Icc (a + ε / 2) (b - ε / 2)).indicator (1 : ℝ → ℝ) y) = b - a - ε := by
    simp only [integral_indicator_one measurableSet_Icc, measureReal_restrict_apply
      measurableSet_Icc, inter_eq_left.mpr hJ, Real.volume_real_Icc]
    convert max_eq_left (show 0 ≤ b - a - ε by linarith) using 1
    ring_nf
  have hiJ : IntegrableOn (fun y : ℝ =>
      (Icc (a + ε / 2) (b - ε / 2)).indicator (1 : ℝ → ℝ) y) (Ioi 0) := by
    have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (a + ε / 2) (b - ε / 2)) :=
      integrableOn_const isCompact_Icc.measure_lt_top.ne
    exact (hi.integrable_indicator measurableSet_Icc).integrableOn
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, fun y => χ.nonneg, hupp, ?_⟩
  · rw [hts]
    exact fun y hy => lt_of_lt_of_le ha hy.1
  · rw [← hint]
    exact setIntegral_mono hiJ
      (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).integrableOn hlow

theorem exists_contDiff_indicator_Ico_le {a b ε : ℝ} (hab : a < b)
    (hε : 0 < ε) (hε' : ε < 2 * a) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ Ioi 0 ∧
      (Ico a b).indicator 1 ≤ ψ ∧ ψ ≤ 1 ∧ (∫ y in Ioi (0 : ℝ), ψ y) ≤ b - a + ε := by
  let χ : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 2, (b - a + ε) / 2, by linarith, by linarith⟩
  have hts : tsupport (χ : ℝ → ℝ) = Icc (a - ε / 2) (b + ε / 2) := by
    rw [χ.tsupport_eq, Real.closedBall_eq_Icc]
    change Icc ((a + b) / 2 - (b - a + ε) / 2)
      ((a + b) / 2 + (b - a + ε) / 2) = _
    ring_nf
  have hsp : Function.support (χ : ℝ → ℝ) = Ioo (a - ε / 2) (b + ε / 2) := by
    rw [χ.support_eq, Real.ball_eq_Ioo]
    change Ioo ((a + b) / 2 - (b - a + ε) / 2)
      ((a + b) / 2 + (b - a + ε) / 2) = _
    ring_nf
  have hlow : (Ico a b).indicator (1 : ℝ → ℝ) ≤ χ := by
    intro y
    by_cases hy : y ∈ Ico a b
    · have hy' : y ∈ Metric.closedBall ((a + b) / 2) χ.rIn := by
        rw [Real.closedBall_eq_Icc]
        change (a + b) / 2 - (b - a) / 2 ≤ y ∧ y ≤ (a + b) / 2 + (b - a) / 2
        constructor <;> linarith [hy.1, hy.2]
      simp only [indicator_of_mem hy, Pi.one_apply, χ.one_of_mem_closedBall hy', le_refl]
    · simpa only [indicator_of_not_mem hy] using χ.nonneg (x := y)
  have hupp : (χ : ℝ → ℝ) ≤ (Ioo (a - ε / 2) (b + ε / 2)).indicator 1 := by
    intro y
    by_cases hy : y ∈ Ioo (a - ε / 2) (b + ε / 2)
    · simpa only [indicator_of_mem hy, Pi.one_apply] using χ.le_one (x := y)
    · have hz : χ y = 0 := by
        by_contra hn
        exact hy (hsp ▸ hn)
      simp only [hz, indicator_of_not_mem hy, le_refl]
  have hJ : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi (0 : ℝ) := by
    intro y hy
    change 0 < y
    linarith [hy.1]
  have hint : (∫ y in Ioi (0 : ℝ),
      (Ioo (a - ε / 2) (b + ε / 2)).indicator (1 : ℝ → ℝ) y) = b - a + ε := by
    simp only [integral_indicator_one measurableSet_Ioo, measureReal_restrict_apply
      measurableSet_Ioo, inter_eq_left.mpr hJ, Real.volume_real_Ioo]
    convert max_eq_left (show 0 ≤ b - a + ε by linarith) using 1
    ring_nf
  have hiJ : IntegrableOn (fun y : ℝ =>
      (Ioo (a - ε / 2) (b + ε / 2)).indicator (1 : ℝ → ℝ) y) (Ioi 0) := by
    have hi : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (a - ε / 2) (b + ε / 2)) :=
      integrableOn_const isCompact_Icc.measure_lt_top.ne
    exact ((hi.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo).integrableOn
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, ?_, hlow, fun y => χ.le_one, ?_⟩
  · rw [hts]
    intro y hy
    change 0 < y
    linarith [hy.1]
  · rw [← hint]
    exact setIntegral_mono
      (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).integrableOn hiJ hupp

end DirichletL
