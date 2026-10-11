import Analysis.GridCellMaximum
import Analysis.ContourCellIntegral

/-!
Exact grid weights for CDT's two-radius integral, supplied TeX 3503-3538 and 8384-8404.
-/

namespace DirichletL

theorem twoRadiusMaxIntegral_le_sortedGridCellSum (ψ : ℂ → ℂ) (r : ℝ)
    {D K : ℕ} (hD : 0 < D) (hK : 0 < K)
    (hf : Continuous (circleLogProfile (fun z => ψ ((r : ℂ) * z))))
    (hg : Continuous (circleLogProfile ψ)) {n m : ℕ} (a b A B : ℕ → ℤ)
    (ha0 : a 0 = 0) (han : a n = (K : ℤ)) (hb0 : b 0 = 0) (hbm : b m = (K : ℤ))
    (ha : ∀ i < n, a i ≤ a (i + 1)) (hb : ∀ j < m, b j ≤ b (j + 1))
    (hA : ∀ i < n, ∀ x ∈ Set.Icc ((a i : ℝ) / K) ((a (i + 1) : ℝ) / K),
      circleLogProfile (fun z => ψ ((r : ℂ) * z)) x ≤ (A i : ℝ) / D)
    (hB : ∀ j < m, ∀ y ∈ Set.Icc ((b j : ℝ) / K) ((b (j + 1) : ℝ) / K),
      circleLogProfile ψ y ≤ (B j : ℝ) / D) :
    twoRadiusMaxIntegral ψ r (209 / 1000) ≤
      ((sortedIntegerMaximum
        (List.ofFn (fun i : Fin n => (A i.1, 209 * (a (i.1 + 1) - a i.1))) ++
          List.ofFn (fun j : Fin m => (B j.1, 791 * (b (j.1 + 1) - b j.1))))).2 : ℝ) /
            ((D : ℝ) * (1000 * (K : ℝ)) ^ 2) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hstarta : (a 0 : ℝ) / K = 0 := by rw [ha0]; simp
  have hstartb : (b 0 : ℝ) / K = 0 := by rw [hb0]; simp
  have henda : (a n : ℝ) / K = 1 := by
    rw [han, Int.cast_natCast, div_self hKr.ne']
  have hendb : (b m : ℝ) / K = 1 := by
    rw [hbm, Int.cast_natCast, div_self hKr.ne']
  have hmonoa : ∀ i < n, (a i : ℝ) / K ≤ (a (i + 1) : ℝ) / K := by
    intro i hi
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha i hi) hKr.le
  have hmonob : ∀ j < m, (b j : ℝ) / K ≤ (b (j + 1) : ℝ) / K := by
    intro j hj
    exact div_le_div_of_nonneg_right (by exact_mod_cast hb j hj) hKr.le
  have hbound := twoRadiusMaxIntegral_le_weightedCellSum ψ r (209 / 1000)
    (by norm_num) (by norm_num) hf hg
    (fun i => (a i : ℝ) / K) (fun j => (b j : ℝ) / K)
    (fun i => (A i : ℝ) / D) (fun j => (B j : ℝ) / D)
    hstarta henda hstartb hendb hmonoa hmonob hA hB
  have hmass (c l u : ℤ) : (c : ℝ) / 1000 * ((u : ℝ) / K - (l : ℝ) / K) =
      ((c * (u - l) : ℤ) : ℝ) / (1000 * (K : ℝ)) := by
    push_cast
    field_simp [hKr.ne']
  let inner (i : Fin n) : ℤ × ℤ := (A i.1, 209 * (a (i.1 + 1) - a i.1))
  let outer (j : Fin m) : ℤ × ℤ := (B j.1, 791 * (b (j.1 + 1) - b j.1))
  have hinner : (fun i : Fin n =>
      (209 / 1000 : ℝ) * ((a (i.1 + 1) : ℝ) / K - (a i.1 : ℝ) / K)) =
      (fun i => ((inner i).2 : ℝ) / (1000 * (K : ℝ))) := by
    funext i
    simpa only [inner, Int.cast_ofNat] using hmass 209 (a i.1) (a (i.1 + 1))
  have houter : (fun j : Fin m =>
      (1 - 209 / 1000 : ℝ) * ((b (j.1 + 1) : ℝ) / K - (b j.1 : ℝ) / K)) =
      (fun j => ((outer j).2 : ℝ) / (1000 * (K : ℝ))) := by
    funext j
    convert hmass 791 (b j.1) (b (j.1 + 1)) using 1
    norm_num [outer]
  dsimp only at hbound
  rw [hinner, houter] at hbound
  exact hbound.trans_eq
    (weightedPairwiseMaxSum_sum_eq_sortedIntegerMaximum inner outer hDr (by positivity))

end DirichletL
