import Analysis.VandermondeCircleBound

/-!
Weighted finite maxima for CDT v2's signed mixture, supplied TeX 3503-3538.
Meanings, sign checks, and the paired reindexing convention precede these bodies
-/

namespace DirichletL

open scoped BigOperators

/-- The signed pairwise maximum sum with a real weight for each finite index. -/
noncomputable def weightedPairwiseMaxSum {ι : Type*} [Fintype ι] (a w : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, w i * w j * max (a i) (a j)

theorem weightedPairwiseMaxSum_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a w : κ → ℝ) :
    weightedPairwiseMaxSum (a ∘ e) (w ∘ e) = weightedPairwiseMaxSum a w := by
  unfold weightedPairwiseMaxSum
  simp only [Function.comp_apply]
  calc
    _ = ∑ i : ι, ∑ j : κ, w (e i) * w j * max (a (e i)) (a j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Equiv.sum_comp e (fun j => w (e i) * w j * max (a (e i)) (a j))
    _ = _ := Equiv.sum_comp e (fun i => ∑ j, w i * w j * max (a i) (a j))

theorem weightedPairwiseMaxSum_sum_elim {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a w : ι → ℝ) (b v : κ → ℝ) :
    weightedPairwiseMaxSum (Sum.elim a b) (Sum.elim w v) =
      weightedPairwiseMaxSum a w +
        2 * (∑ i, ∑ j, w i * v j * max (a i) (b j)) + weightedPairwiseMaxSum b v := by
  have hcross : (∑ j : κ, ∑ i : ι, v j * w i * max (b j) (a i)) =
      ∑ i : ι, ∑ j : κ, w i * v j * max (a i) (b j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [max_comm (b j) (a i)]
    ring
  unfold weightedPairwiseMaxSum
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
  rw [hcross]
  ring

theorem weightedPairwiseMaxSum_eq_sum_of_monotone {d : ℕ} (a w : Fin d → ℝ)
    (ha : Monotone a) :
    weightedPairwiseMaxSum a w =
      ∑ i, a i * ((w i) ^ 2 + 2 * w i * ∑ j ∈ Finset.Iio i, w j) := by
  classical
  let f (i j : Fin d) : ℝ := w i * w j * max (a i) (a j)
  have hsym (i j : Fin d) : f i j = f j i := by
    dsimp only [f]
    rw [max_comm (a i) (a j)]
    ring
  have hsplit := sum_sum_eq_diag_add_two_mul_sum_Ioi f hsym
  change weightedPairwiseMaxSum a w = (∑ i, f i i) +
    2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j at hsplit
  have hdiag : (∑ i, f i i) = ∑ i, a i * (w i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [f, max_self]
    ring
  have hIoi (i : Fin d) : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
    ext j
    simp [Finset.mem_Ioi]
  have hIio (j : Fin d) : Finset.Iio j = Finset.univ.filter (fun i => i < j) := by
    ext i
    simp [Finset.mem_Iio]
  have hoff : (∑ i, ∑ j ∈ Finset.Ioi i, f i j) =
      ∑ i, a i * w i * ∑ j ∈ Finset.Iio i, w j := by
    calc
      _ = ∑ i, ∑ j ∈ Finset.Ioi i, a j * w j * w i := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        dsimp only [f]
        rw [max_eq_right (ha (Finset.mem_Ioi.mp hj).le)]
        ring
      _ = ∑ j, ∑ i ∈ Finset.Iio j, a j * w j * w i := by
        simp_rw [hIoi, Finset.sum_filter]
        rw [Finset.sum_comm]
        simp_rw [hIio, Finset.sum_filter]
      _ = _ := by simp only [Finset.mul_sum]
  rw [hsplit, hdiag, hoff, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end DirichletL
