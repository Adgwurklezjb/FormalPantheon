import Analysis.SortedIntegerMaximum

/-!
Tagged cell entries for CDT's signed finite maximum, supplied TeX 3503-3538 and 8384-8404.
-/

namespace DirichletL

theorem weightedPairwiseMaxSum_sum_eq_sortedIntegerMaximum {n m : ℕ}
    (inner : Fin n → ℤ × ℤ) (outer : Fin m → ℤ × ℤ)
    {D L : ℝ} (hD : 0 < D) (hL : 0 < L) :
    weightedPairwiseMaxSum
      (Sum.elim (fun i => ((inner i).1 : ℝ) / D) (fun j => ((outer j).1 : ℝ) / D))
      (Sum.elim (fun i => ((inner i).2 : ℝ) / L) (fun j => ((outer j).2 : ℝ) / L)) =
        ((sortedIntegerMaximum (List.ofFn inner ++ List.ofFn outer)).2 : ℝ) / (D * L ^ 2) := by
  let F := Fin.append inner outer
  have hvalues : (fun i : Fin (n + m) => ((F i).1 : ℝ) / D) ∘ finSumFinEquiv =
      Sum.elim (fun i => ((inner i).1 : ℝ) / D) (fun j => ((outer j).1 : ℝ) / D) := by
    funext i
    rcases i with i | j <;> simp [F, Function.comp_def]
  have hweights : (fun i : Fin (n + m) => ((F i).2 : ℝ) / L) ∘ finSumFinEquiv =
      Sum.elim (fun i => ((inner i).2 : ℝ) / L) (fun j => ((outer j).2 : ℝ) / L) := by
    funext i
    rcases i with i | j <;> simp [F, Function.comp_def]
  have hreindex := weightedPairwiseMaxSum_comp_equiv finSumFinEquiv
    (fun i : Fin (n + m) => ((F i).1 : ℝ) / D)
    (fun i : Fin (n + m) => ((F i).2 : ℝ) / L)
  rw [hvalues, hweights] at hreindex
  have hlist : weightedPairwiseMaxSum
      (fun i : Fin (List.ofFn F).length => ((List.ofFn F)[i.1].1 : ℝ) / D)
      (fun i : Fin (List.ofFn F).length => ((List.ofFn F)[i.1].2 : ℝ) / L) =
      weightedPairwiseMaxSum (fun i => ((F i).1 : ℝ) / D)
        (fun i => ((F i).2 : ℝ) / L) := by
    let e : Fin (List.ofFn F).length ≃ Fin (n + m) := finCongr List.length_ofFn
    have he (i : Fin (List.ofFn F).length) : (List.ofFn F)[i.1] = F (e i) := by
      rw [List.getElem_ofFn]
      rfl
    simpa only [Function.comp_def, he] using
      weightedPairwiseMaxSum_comp_equiv e
        (fun i => ((F i).1 : ℝ) / D) (fun i => ((F i).2 : ℝ) / L)
  have h := weightedPairwiseMaxSum_eq_sortedIntegerMaximum (List.ofFn F) hD hL
  rw [hlist] at h
  simpa only [F, List.ofFn_fin_append] using hreindex.trans h

end DirichletL
