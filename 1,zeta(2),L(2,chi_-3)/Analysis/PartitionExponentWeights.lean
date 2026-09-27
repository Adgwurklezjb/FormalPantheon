import Analysis.PartitionBlockMoments
import Analysis.AuxiliaryExponentStatistics
import Analysis.BlockVandermondeBound

/-!
Signed block weights for CDT v2, supplied TeX 3998-4028.
-/

namespace DirichletL

theorem HasIntervalDiscrepancyLE.abs_sum_subset_sub_rightGrid_le
    {d : ℕ} {t : Fin d → ℝ} {ε : ℝ} (h : HasIntervalDiscrepancyLE t ε)
    (hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hmono : Monotone t)
    (S : Finset (Fin d)) :
    |(∑ i ∈ S, t i) - (∑ i ∈ S, ((i.val : ℝ) + 1) / d)| ≤ (S.card : ℝ) * ε := by
  obtain ⟨hlower, hupper⟩ := h.sum_subset_bounds hcube hmono S
  have hgrid : (∑ i ∈ S, (i.val : ℝ) / d) ≤
      ∑ i ∈ S, ((i.val : ℝ) + 1) / d := by
    apply Finset.sum_le_sum
    intro i _
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg d)
  apply abs_le.mpr
  constructor <;> linarith only [hlower, hupper, hgrid]

theorem HasIntervalDiscrepancyLE.abs_two_mul_sum_partition_block_sub_le
    {s d : ℕ} {t : Fin d → ℝ} {ε : ℝ} (h : HasIntervalDiscrepancyLE t ε)
    (hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hmono : Monotone t)
    (hs : 0 < s) (hd : 0 < d) (a : Fin (s + 1) → ℝ) (ha : Monotone a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1) (b : Fin d → Fin s)
    (hb : ∀ i q, b i = q ↔ a q.castSucc * d ≤ (i.val : ℝ) + 1 ∧
      ((i.val : ℝ) + 1 < a q.succ * d ∨ q.succ = Fin.last s)) (q : Fin s) :
    |2 * (∑ i ∈ Finset.univ.filter (fun i => b i = q), t i) / d -
      (a q.succ ^ 2 - a q.castSucc ^ 2)| ≤
        2 * (((Finset.univ.filter (fun i => b i = q)).card : ℝ) / d) * ε + 3 / (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let S : Finset (Fin d) := Finset.univ.filter (fun i => b i = q)
  let T : ℝ := ∑ i ∈ S, t i
  let U : ℝ := ∑ i ∈ S, ((i.val : ℝ) + 1) / d
  have hbase : |T - U| ≤ (S.card : ℝ) * ε :=
    h.abs_sum_subset_sub_rightGrid_le hcube hmono S
  have hround : |2 * U / d - (a q.succ ^ 2 - a q.castSucc ^ 2)| ≤ 3 / (d : ℝ) :=
    abs_two_mul_sum_partitionBlock_grid_sub_sq_sub_le hs hd a ha ha0 ha1 b hb q
  have hscale : 0 ≤ 2 / (d : ℝ) := div_nonneg (by norm_num) hdR.le
  have hdiff : |2 * T / d - 2 * U / d| ≤ 2 * ((S.card : ℝ) / d) * ε := by
    have hfactor : 2 * T / d - 2 * U / d = (2 / (d : ℝ)) * (T - U) := by ring
    rw [hfactor, abs_mul, abs_of_nonneg hscale]
    calc
      _ ≤ (2 / (d : ℝ)) * ((S.card : ℝ) * ε) :=
        mul_le_mul_of_nonneg_left hbase hscale
      _ = _ := by ring
  exact (abs_sub_le (2 * T / d) (2 * U / d) _).trans (add_le_add hdiff hround)

theorem HasIntervalDiscrepancyLE.abs_two_mul_sum_partition_weights_sub_le
    {s d : ℕ} {t : Fin d → ℝ} {ε : ℝ} (h : HasIntervalDiscrepancyLE t ε)
    (hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1) (hmono : Monotone t)
    (hs : 0 < s) (hd : 0 < d) (a : Fin (s + 1) → ℝ) (ha : Monotone a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1) (b : Fin d → Fin s)
    (hb : ∀ i q, b i = q ↔ a q.castSucc * d ≤ (i.val : ℝ) + 1 ∧
      ((i.val : ℝ) + 1 < a q.succ * d ∨ q.succ = Fin.last s))
    (ℓ : Fin s → ℝ) {K : ℝ} (hK : ∀ q, |ℓ q| ≤ K) :
    |2 * (∑ i, t i * ℓ (b i)) / d -
      ∑ q, (a q.succ ^ 2 - a q.castSucc ^ 2) * ℓ q| ≤
        2 * ε * K + 3 * (s : ℝ) * K / d := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let S (q : Fin s) : Finset (Fin d) := Finset.univ.filter (fun i => b i = q)
  let T (q : Fin s) : ℝ := ∑ i ∈ S q, t i
  let α (q : Fin s) : ℝ := ((S q).card : ℝ) / d
  let w (q : Fin s) : ℝ := a q.succ ^ 2 - a q.castSucc ^ 2
  have hcardNat : ∑ q, (S q).card = d := sum_card_block_fibers b
  have hcard : ∑ q, ((S q).card : ℝ) = (d : ℝ) := by exact_mod_cast hcardNat
  have hαsum : ∑ q, α q = 1 := by
    simp only [α, ← Finset.sum_div, hcard, div_self hdR.ne']
  have herror (q : Fin s) : |2 * T q / d - w q| ≤ 2 * α q * ε + 3 / (d : ℝ) :=
    h.abs_two_mul_sum_partition_block_sub_le hcube hmono hs hd a ha ha0 ha1 b hb q
  have hsplit : (∑ i, t i * ℓ (b i)) = ∑ q, T q * ℓ q := by
    rw [← Finset.sum_fiberwise Finset.univ b (fun i => t i * ℓ (b i))]
    apply Finset.sum_congr rfl
    intro q _
    dsimp only [T, S]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hform : 2 * (∑ i, t i * ℓ (b i)) / d - ∑ q, w q * ℓ q =
      ∑ q, (2 * T q / d - w q) * ℓ q := by
    rw [hsplit, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  change |2 * (∑ i, t i * ℓ (b i)) / d - ∑ q, w q * ℓ q| ≤ _
  rw [hform]
  calc
    _ ≤ ∑ q, |(2 * T q / d - w q) * ℓ q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, (2 * α q * ε + 3 / (d : ℝ)) * K := by
      apply Finset.sum_le_sum
      intro q _
      rw [abs_mul]
      exact mul_le_mul (herror q) (hK q) (abs_nonneg _)
        ((abs_nonneg _).trans (herror q))
    _ = 2 * ε * K + 3 * (s : ℝ) * K / d := by
      simp only [add_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        hαsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        one_mul, mul_one]
      ring

end DirichletL
