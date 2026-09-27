import Analysis.PartitionCuts

/-!
The actual consecutive blocks in CDT v2, supplied TeX 3998-4028 and
4150-4179. The endpoint rule and order of the positive-proportion constants
-/

namespace DirichletL

theorem exists_partition_block_map {s : ℕ} (hs : 0 < s)
    (a : Fin (s + 1) → ℝ) (ha : Monotone a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1) (d : ℕ) :
    ∃ b : Fin d → Fin s,
      (∀ i q, b i = q ↔ a q.castSucc * d ≤ (i.val : ℝ) + 1 ∧
        ((i.val : ℝ) + 1 < a q.succ * d ∨ q.succ = Fin.last s)) ∧
      ∀ q, |((Finset.univ.filter (fun i => b i = q)).card : ℝ) -
        (a q.succ - a q.castSucc) * d| ≤ 1 := by
  obtain ⟨b, hb⟩ := exists_consecutiveBlock_map (partitionCut a d)
    (monotone_partitionCut ha ha1 d) (partitionCut_zero a d) (partitionCut_last hs a d)
  have hfiber (q : Fin s) : Finset.univ.filter (fun i => b i = q) =
      consecutiveBlock (partitionCut a d) q := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hb]
  refine ⟨b, ?_, ?_⟩
  · intro i q
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
    rw [hb, mem_consecutiveBlock, partitionCut_le_iff ha0 _ hfirst]
    by_cases hlast : q.succ = Fin.last s
    · simp only [hlast, partitionCut_last hs a d, i.isLt, or_true, and_true]
    · rw [lt_partitionCut_iff _ hzero hlast]
      simp only [hlast, or_false]
  · intro q
    rw [hfiber, card_consecutiveBlock _ _ (partitionCut_le_dim ha ha1 d q.succ)]
    exact abs_consecutiveBlockSize_sub_mul_sub_le_one
      (monotone_partitionCut ha ha1 d) (partitionCut_bounds ha ha0 ha1 d) q

theorem exists_partition_block_proportions {s : ℕ} (hs : 0 < s)
    (a : Fin (s + 1) → ℝ) (ha : StrictMono a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ b : Fin d → Fin s,
      (∀ i q, b i = q ↔ a q.castSucc * d ≤ (i.val : ℝ) + 1 ∧
        ((i.val : ℝ) + 1 < a q.succ * d ∨ q.succ = Fin.last s)) ∧
      (∀ q, |((Finset.univ.filter (fun i => b i = q)).card : ℝ) -
        (a q.succ - a q.castSucc) * d| ≤ 1) ∧
      ∀ q, ρ * d ≤ ((Finset.univ.filter (fun i => b i = q)).card : ℝ) := by
  have hwidth (q : Fin s) : (0 : ℝ) < a q.succ - a q.castSucc :=
    sub_pos.mpr (ha (Fin.castSucc_lt_succ q))
  obtain ⟨w, hw, hwp⟩ := Pi.exists_forall_pos_add_lt hwidth
  refine ⟨w / 2, by positivity, ⌈2 / w⌉₊, ?_⟩
  intro d hd
  obtain ⟨b, hb, hcard⟩ := exists_partition_block_map hs a ha.monotone ha0 ha1 d
  refine ⟨b, hb, hcard, fun q => ?_⟩
  apply consecutiveBlockSize_ge_half_width hw (by simpa only [zero_add] using (hwp q).le)
    (hcard q)
  exact (Nat.le_ceil (2 / w)).trans (by exact_mod_cast hd)

end DirichletL
