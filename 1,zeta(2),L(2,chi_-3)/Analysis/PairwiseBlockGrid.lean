import Analysis.PairwiseMaximumGrid
import Analysis.BlockGridValues
import Analysis.PairwiseMaximumIntegral
import Analysis.FiniteProductWeights
import Analysis.BlockVandermondeBound

/-!
The literal block statistic in CDT v2, supplied TeX 3503-3540 and
4150-4228. Meanings and empty-block checks precede these bodies in
-/

namespace DirichletL

theorem pairwiseMaxSum_blockGridValues {κ : Type*} [Fintype κ] [DecidableEq κ]
    {d : ℕ} (b : Fin d → κ) (f : κ → ℝ → ℝ) :
    let n : κ → ℕ := fun q => (Finset.univ.filter (fun i => b i = q)).card
    pairwiseMaxSum (blockGridValues b f) =
      ∑ q, ∑ r, ∑ i : Fin (n q), ∑ j : Fin (n r),
        max (f q (((i.val : ℝ) + 1) / n q)) (f r (((j.val : ℝ) + 1) / n r)) := by
  classical
  let n : κ → ℕ := fun q => (Finset.univ.filter (fun i => b i = q)).card
  let E : (Σ q, Fin (n q)) ≃ Fin d := blockIndexEquiv b
  have hvalues (q : κ) (i : Fin (n q)) :
      blockGridValues b f (E ⟨q, i⟩) = f q (((i.val : ℝ) + 1) / n q) := by
    dsimp only [E]
    rw [blockIndexEquiv_apply, blockGridValues_orderEmbOfFin]
  have hinner (u : Fin d) :
      (∑ v, max (blockGridValues b f u) (blockGridValues b f v)) =
        ∑ r, ∑ j : Fin (n r),
          max (blockGridValues b f u) (f r (((j.val : ℝ) + 1) / n r)) := by
    calc
      _ = ∑ rj : Σ r, Fin (n r),
          max (blockGridValues b f u) (blockGridValues b f (E rj)) :=
        (Equiv.sum_comp E _).symm
      _ = _ := by simp only [Fintype.sum_sigma, hvalues]
  calc
    pairwiseMaxSum (blockGridValues b f) =
        ∑ u : Fin d, ∑ r, ∑ j : Fin (n r),
          max (blockGridValues b f u) (f r (((j.val : ℝ) + 1) / n r)) := by
      simp only [pairwiseMaxSum, hinner]
    _ = ∑ qi : Σ q, Fin (n q), ∑ r, ∑ j : Fin (n r),
        max (blockGridValues b f (E qi)) (f r (((j.val : ℝ) + 1) / n r)) :=
      (Equiv.sum_comp E _).symm
    _ = ∑ q, ∑ i : Fin (n q), ∑ r, ∑ j : Fin (n r),
        max (f q (((i.val : ℝ) + 1) / n q)) (f r (((j.val : ℝ) + 1) / n r)) := by
      simp only [Fintype.sum_sigma, hvalues]
    _ = ∑ q, ∑ r, ∑ i : Fin (n q), ∑ j : Fin (n r),
        max (f q (((i.val : ℝ) + 1) / n q)) (f r (((j.val : ℝ) + 1) / n r)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact Finset.sum_comm

theorem pairwiseMaxSum_blockGridValues_div_sq {κ : Type*} [Fintype κ] [DecidableEq κ]
    {d : ℕ} (b : Fin d → κ) (f : κ → ℝ → ℝ)
    (hsize : ∀ q, 0 < (Finset.univ.filter (fun i => b i = q)).card) :
    pairwiseMaxSum (blockGridValues b f) / (d : ℝ) ^ 2 =
      ∑ q, ∑ r,
        (((Finset.univ.filter (fun i => b i = q)).card : ℝ) / d) *
        (((Finset.univ.filter (fun i => b i = r)).card : ℝ) / d) *
          pairwiseMaxGridAverage (f q) (f r)
            (Finset.univ.filter (fun i => b i = q)).card
            (Finset.univ.filter (fun i => b i = r)).card := by
  classical
  have hn (q : κ) : (0 : ℝ) < (Finset.univ.filter (fun i => b i = q)).card := by
    exact_mod_cast hsize q
  rw [pairwiseMaxSum_blockGridValues, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r _
  dsimp only [pairwiseMaxGridAverage]
  by_cases hd : (d : ℝ) = 0
  · simp [hd]
  field_simp [hd, (hn q).ne', (hn r).ne']

theorem abs_two_mul_sortedGridSum_block_sub_integral_le
    {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℕ}
    (b : Fin d → κ) (f : κ → ℝ → ℝ) (hd : 0 < d)
    (hsize : ∀ q, 0 < (Finset.univ.filter (fun i => b i = q)).card)
    (p : κ → ℝ) (hp : ∀ q, 0 ≤ p q) (hpsum : ∑ q, p q = 1)
    (hcard : ∀ q, |((Finset.univ.filter (fun i => b i = q)).card : ℝ) - p q * d| ≤ 1)
    {ξ B : ℝ} (hB : 0 ≤ B)
    (hfB : ∀ q u, u ∈ Set.Icc (0 : ℝ) 1 → |f q u| ≤ B)
    (hgrid : ∀ q r,
      |pairwiseMaxGridAverage (f q) (f r)
        (Finset.univ.filter (fun i => b i = q)).card
        (Finset.univ.filter (fun i => b i = r)).card - pairwiseMaxIntegral (f q) (f r)| ≤ 2 * ξ) :
    |2 * sortedGridSum (blockGridValues b f) / d -
      ∑ q, ∑ r, p q * p r * pairwiseMaxIntegral (f q) (f r)| ≤
        2 * ξ + (1 + 2 * Fintype.card κ) * B / d := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let n : κ → ℕ := fun q => (Finset.univ.filter (fun i => b i = q)).card
  let α (q : κ) : ℝ := (n q : ℝ) / d
  let A (q r : κ) : ℝ := pairwiseMaxGridAverage (f q) (f r) (n q) (n r)
  let I (q r : κ) : ℝ := pairwiseMaxIntegral (f q) (f r)
  have hα (q : κ) : 0 ≤ α q := div_nonneg (Nat.cast_nonneg _) hdR.le
  have hnsum : ∑ q, n q = d := sum_card_block_fibers b
  have hnsumR : ∑ q, (n q : ℝ) = (d : ℝ) := by exact_mod_cast hnsum
  have hαsum : ∑ q, α q = 1 := by
    simp only [α, ← Finset.sum_div, hnsumR, div_self hdR.ne']
  have hαerror (q : κ) : |α q - p q| ≤ 1 / (d : ℝ) := by
    have hquot : α q - p q = ((n q : ℝ) - p q * d) / d := by
      dsimp only [α]
      field_simp [hdR.ne']
    rw [hquot, abs_div, abs_of_pos hdR]
    exact div_le_div_of_nonneg_right (hcard q) hdR.le
  have hsumerror : (∑ q, |α q - p q|) ≤ (Fintype.card κ : ℝ) / d := by
    calc
      _ ≤ ∑ _q : κ, 1 / (d : ℝ) := Finset.sum_le_sum (fun q _ => hαerror q)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hnormalize := pairwiseMaxSum_blockGridValues_div_sq b f hsize
  change pairwiseMaxSum (blockGridValues b f) / (d : ℝ) ^ 2 =
    ∑ q, ∑ r, α q * α r * A q r at hnormalize
  have hmass := abs_weighted_pair_sum_sub_le α p hα hp hαsum hpsum A I hB hgrid
    (fun q r => abs_pairwiseMaxIntegral_le (hfB q) (hfB r))
  have hmean : |pairwiseMaxSum (blockGridValues b f) / (d : ℝ) ^ 2 -
      ∑ q, ∑ r, p q * p r * I q r| ≤ 2 * ξ + 2 * B * ((Fintype.card κ : ℝ) / d) := by
    rw [hnormalize]
    exact hmass.trans (add_le_add_left
      (mul_le_mul_of_nonneg_left hsumerror (by positivity)) (2 * ξ))
  have hdiag := abs_two_mul_sortedGridSum_div_sub_pairwiseMaxSum_div_sq_le hd
    (blockGridValues b f) (abs_blockGridValues_le b f hfB)
  calc
    _ ≤ |2 * sortedGridSum (blockGridValues b f) / d -
          pairwiseMaxSum (blockGridValues b f) / (d : ℝ) ^ 2| +
        |pairwiseMaxSum (blockGridValues b f) / (d : ℝ) ^ 2 -
          ∑ q, ∑ r, p q * p r * I q r| := abs_sub_le _ _ _
    _ ≤ B / d + (2 * ξ + 2 * B * ((Fintype.card κ : ℝ) / d)) := add_le_add hdiag hmean
    _ = 2 * ξ + (1 + 2 * Fintype.card κ) * B / d := by ring

end DirichletL
