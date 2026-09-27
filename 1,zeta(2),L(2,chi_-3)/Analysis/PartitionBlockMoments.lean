import Analysis.ConsecutiveBlockMoments
import Analysis.PartitionCuts

/-!
The exact paper blocks and their first moments, CDT v2 TeX 3998-4028.
-/

namespace DirichletL

theorem partition_block_fiber_eq_consecutiveBlock {s d : ℕ} (hs : 0 < s)
    (a : Fin (s + 1) → ℝ) (ha0 : a 0 = 0) (b : Fin d → Fin s)
    (hb : ∀ i q, b i = q ↔ a q.castSucc * d ≤ (i.val : ℝ) + 1 ∧
      ((i.val : ℝ) + 1 < a q.succ * d ∨ q.succ = Fin.last s)) (q : Fin s) :
    Finset.univ.filter (fun i => b i = q) = consecutiveBlock (partitionCut a d) q := by
  ext i
  have hfirst : q.castSucc ≠ Fin.last s := by
    intro h
    have hv := congrArg Fin.val h
    change q.val = s at hv
    exact q.isLt.ne hv
  have hzero : q.succ ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_zero] at hv
    omega
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hb, mem_consecutiveBlock]
  rw [partitionCut_le_iff ha0 _ hfirst]
  by_cases hlast : q.succ = Fin.last s
  · simp only [hlast, partitionCut_last hs a d, i.isLt, or_true, and_true]
  · rw [lt_partitionCut_iff _ hzero hlast]
    simp only [hlast, or_false]

theorem abs_two_mul_sum_partitionBlock_grid_sub_sq_sub_le {s d : ℕ}
    (hs : 0 < s) (hd : 0 < d) (a : Fin (s + 1) → ℝ) (ha : Monotone a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1) (b : Fin d → Fin s)
    (hb : ∀ i q, b i = q ↔ a q.castSucc * d ≤ (i.val : ℝ) + 1 ∧
      ((i.val : ℝ) + 1 < a q.succ * d ∨ q.succ = Fin.last s)) (q : Fin s) :
    |2 * (∑ i ∈ Finset.univ.filter (fun i => b i = q),
      (((i.val : ℝ) + 1) / d)) / d - (a q.succ ^ 2 - a q.castSucc ^ 2)| ≤ 3 / (d : ℝ) := by
  let c := partitionCut a d
  have hmoment := sum_consecutiveBlock_val_succ c q
    (monotone_partitionCut ha ha1 d (Fin.castSucc_lt_succ q).le)
    (partitionCut_le_dim ha ha1 d q.succ)
  have hgrid : 2 * (∑ i ∈ Finset.univ.filter (fun i => b i = q),
      (((i.val : ℝ) + 1) / d)) / d =
      (c q.succ : ℝ) * ((c q.succ : ℝ) + 1) / (d : ℝ) ^ 2 -
        (c q.castSucc : ℝ) * ((c q.castSucc : ℝ) + 1) / (d : ℝ) ^ 2 := by
    rw [partition_block_fiber_eq_consecutiveBlock hs a ha0 b hb q, ← Finset.sum_div]
    calc
      _ = (2 * ∑ i ∈ consecutiveBlock (d := d) c q, ((i.val : ℝ) + 1)) /
          (d : ℝ) ^ 2 := by ring
      _ = _ := by rw [hmoment]; ring
  have hbound (r : Fin (s + 1)) :
      -(2 / (d : ℝ)) ≤ (c r : ℝ) * ((c r : ℝ) + 1) / (d : ℝ) ^ 2 - a r ^ 2 ∧
        (c r : ℝ) * ((c r : ℝ) + 1) / (d : ℝ) ^ 2 - a r ^ 2 ≤ 1 / (d : ℝ) :=
    normalized_cut_moment_bounds hd
      (by simpa only [ha0] using ha (Fin.zero_le r))
      (by simpa only [ha1] using ha (Fin.le_last r))
      (partitionCut_bounds ha ha0 ha1 d r)
  rw [hgrid]
  apply abs_le.mpr
  simp only [div_eq_mul_inv] at hbound ⊢
  constructor <;> linarith only [(hbound q.succ).1, (hbound q.succ).2,
    (hbound q.castSucc).1, (hbound q.castSucc).2]

end DirichletL
