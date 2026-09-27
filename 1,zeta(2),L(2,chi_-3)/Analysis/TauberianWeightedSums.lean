import Analysis.TauberianKernel

/-!
Weighted sums for the Wiener-Ikehara route to CDT v2's lcm input
(supplied TeX 3291-3310). Based on the PrimeNumberTheoremAnd contributors,
Wiener.lean at revision 0766218b21b11ddf24103352ece7f0cb730945e0,
lines 1208-1476; its source and Apache 2.0 license are archived in
partition use canonical Mathlib APIs. Summability follows directly
from the finite bound, before the later boundary-limit argument.
-/

namespace DirichletL

open MeasureTheory Filter Set
open scoped Topology

theorem sum_mul_le_of_sum_range_le {u g : ℕ → ℝ} {C : ℝ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, u i ≤ C * n)
    (hg : ∀ n, 0 ≤ g n) (hmono : Antitone g) (n : ℕ) :
    (∑ i ∈ Finset.range n, u i * g i) ≤ C * ∑ i ∈ Finset.range n, g i := by
  have hconst (k : ℕ) : (∑ i ∈ Finset.range k, u i) ≤ ∑ _i ∈ Finset.range k, C := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using hsum k
  calc
    (∑ i ∈ Finset.range n, u i * g i) = ∑ i ∈ Finset.range n, g i • u i := by
      simp only [smul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ Finset.range n, g i • C := by
      rw [Finset.sum_range_by_parts g u n,
        Finset.sum_range_by_parts g (fun _ : ℕ => C) n]
      apply sub_le_sub
      · exact mul_le_mul_of_nonneg_left (hconst n) (hg _)
      · apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonpos_left (hconst (i + 1))
          (sub_nonpos.mpr (hmono (Nat.le_succ i)))
    _ = C * ∑ i ∈ Finset.range n, g i := by
      simp only [smul_eq_mul, Finset.mul_sum, mul_comm]

theorem sum_le_integral_of_antitoneOn_Ioc {f : ℝ → ℝ} (a : ℝ) (n : ℕ)
    (hf : AntitoneOn f (Ioc a (a + n))) (hfi : IntegrableOn f (Icc a (a + n))) :
    (∑ i ∈ Finset.range n, f (a + (i + 1 : ℕ))) ≤ ∫ t in a..a + n, f t := by
  have hint (i : ℕ) (hi : i < n) :
      IntervalIntegrable f volume (a + i) (a + (i + 1 : ℕ)) := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le (add_le_add_left (by exact_mod_cast Nat.le_succ i) a)]
    apply hfi.mono_set
    exact Icc_subset_Icc (le_add_of_nonneg_right (Nat.cast_nonneg i))
      (add_le_add_left (by exact_mod_cast Nat.succ_le_of_lt hi) a)
  calc
    (∑ i ∈ Finset.range n, f (a + (i + 1 : ℕ))) =
        ∑ i ∈ Finset.range n, ∫ _t in a + i..a + (i + 1 : ℕ), f (a + (i + 1 : ℕ)) := by
      simp
    _ ≤ ∑ i ∈ Finset.range n, ∫ t in a + i..a + (i + 1 : ℕ), f t := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
      have hupper : a + (i + 1 : ℕ) ≤ a + n :=
        add_le_add_left (by exact_mod_cast hin) a
      apply intervalIntegral.integral_mono_on_of_le_Ioo
        (add_le_add_left (by exact_mod_cast Nat.le_succ i) a)
        intervalIntegrable_const (hint i (Finset.mem_range.mp hi))
      intro t ht
      apply hf ⟨?_, ht.2.le.trans hupper⟩ ⟨?_, hupper⟩ ht.2.le
      · exact (le_add_of_nonneg_right (Nat.cast_nonneg i)).trans_lt ht.1
      · exact lt_add_of_pos_right a (by positivity)
    _ = ∫ t in a..a + n, f t := by
      simpa only [Nat.cast_zero, add_zero] using
        intervalIntegral.sum_integral_adjacent_intervals hint

/-- The natural-index weight with zeroth value increased to one. -/
noncomputable def tauberianNatWeight (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else tauberianWeight x n

theorem tauberianNatWeight_nonneg (x : ℝ) (n : ℕ) : 0 ≤ tauberianNatWeight x n := by
  by_cases hn : n = 0
  · simp [tauberianNatWeight, hn]
  · simpa only [tauberianNatWeight, if_neg hn] using
      tauberianWeight_nonneg x (Nat.cast_nonneg n)

theorem antitone_tauberianNatWeight {x : ℝ} (hx : 0 < x) :
    Antitone (tauberianNatWeight x) := by
  intro i j hij
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · simp [tauberianNatWeight, hi, hj]
    · simpa [tauberianNatWeight, hi, hj] using tauberianWeight_nat_le_one x j
  have hj : j ≠ 0 := Nat.ne_of_gt ((Nat.pos_of_ne_zero hi).trans_le hij)
  simpa only [tauberianNatWeight, if_neg hi, if_neg hj] using
    antitoneOn_tauberianWeight hx
      (show (0 : ℝ) < i by exact_mod_cast Nat.pos_of_ne_zero hi)
      (show (0 : ℝ) < j by exact_mod_cast Nat.pos_of_ne_zero hj)
      (by exact_mod_cast hij)

theorem sum_tauberianNatWeight_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∑ i ∈ Finset.range n, tauberianNatWeight x i) ≤ 1 + 2 * Real.pi ^ 2 := by
  cases n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
  | succ n =>
    have hsum : (∑ i ∈ Finset.range (n + 1), tauberianNatWeight x i) =
        1 + ∑ i ∈ Finset.range n, tauberianWeight x (i + 1 : ℕ) := by
      rw [Finset.sum_range_succ']
      simp [tauberianNatWeight, add_comm]
    rw [hsum]
    apply add_le_add_left
    obtain ⟨hi, hv⟩ := integrableOn_tauberianWeight_and_integral hx
    have hbound := sum_le_integral_of_antitoneOn_Ioc 0 n
      ((antitoneOn_tauberianWeight hx).mono Ioc_subset_Ioi_self)
      (hi.mono_set Icc_subset_Ici_self)
    simp only [zero_add] at hbound
    apply hbound.trans
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n), ← hv]
    apply integral_mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl)
    · exact (ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => tauberianWeight_nonneg x ht.le)
    · exact hi.mono_set Ioi_subset_Ici_self

theorem sum_norm_mul_tauberianWeight_le {f : ℕ → ℂ} {C : ℝ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖f i‖ * tauberianWeight x i) ≤ C * (1 + 2 * Real.pi ^ 2) := by
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (by simpa using hsum 1)
  calc
    (∑ i ∈ Finset.range n, ‖f i‖ * tauberianWeight x i) ≤
        ∑ i ∈ Finset.range n, ‖f i‖ * tauberianNatWeight x i := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      by_cases hi : i = 0
      · simp [tauberianNatWeight, hi, tauberianWeight_zero]
      · simp [tauberianNatWeight, hi]
    _ ≤ C * ∑ i ∈ Finset.range n, tauberianNatWeight x i :=
      sum_mul_le_of_sum_range_le hsum (tauberianNatWeight_nonneg x)
        (antitone_tauberianNatWeight hx) n
    _ ≤ C * (1 + 2 * Real.pi ^ 2) := mul_le_mul_of_nonneg_left (sum_tauberianNatWeight_le hx n) hC

theorem summable_norm_mul_tauberianWeight {f : ℕ → ℂ} {C : ℝ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n) {x : ℝ} (hx : 0 < x) :
    Summable (fun i : ℕ => ‖f i‖ * tauberianWeight x i) :=
  summable_of_sum_range_le
    (fun i => mul_nonneg (norm_nonneg _) (tauberianWeight_nonneg x (Nat.cast_nonneg i)))
    (sum_norm_mul_tauberianWeight_le hsum hx)

theorem tsum_norm_mul_tauberianWeight_le {f : ℕ → ℂ} {C : ℝ}
    (hsum : ∀ n, ∑ i ∈ Finset.range n, ‖f i‖ ≤ C * n) {x : ℝ} (hx : 0 < x) :
    (∑' i : ℕ, ‖f i‖ * tauberianWeight x i) ≤ C * (1 + 2 * Real.pi ^ 2) :=
  (summable_norm_mul_tauberianWeight hsum hx).tsum_le_of_sum_range_le
    (sum_norm_mul_tauberianWeight_le hsum hx)

end DirichletL
