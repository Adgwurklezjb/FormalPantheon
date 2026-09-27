import Analysis.ContourCellPartition
import Analysis.GridContourIntegral

/-!
Complete list certificates for CDT's signed two-radius integral, author page 174;
supplied TeX 3503–3538 and 8384–8404. Meanings and paired-index checks precede
-/

namespace DirichletL

theorem twoRadiusMaxIntegral_le_sortedContourCells {D K : ℕ}
    (hD : 0 < D) (hK : 0 < K) (inner outer : List ContourGridCell)
    (hi0 : inner.head?.map ContourGridCell.left = some 0)
    (hiK : inner.getLast?.map ContourGridCell.right = some (K : ℤ))
    (ho0 : outer.head?.map ContourGridCell.left = some 0)
    (hoK : outer.getLast?.map ContourGridCell.right = some (K : ℤ))
    (hichain : inner.Chain' (fun c d => c.right = d.left))
    (hochain : outer.Chain' (fun c d => c.right = d.left))
    (hiorder : ∀ cell ∈ inner, cell.left ≤ cell.right)
    (hoorder : ∀ cell ∈ outer, cell.left ≤ cell.right)
    (hibound : ∀ cell ∈ inner, ContourGridCell.Bounded D K true cell)
    (hobound : ∀ cell ∈ outer, ContourGridCell.Bounded D K false cell) :
    twoRadiusMaxIntegral cdtContourMap (Real.exp (-1 / 2)) (209 / 1000) ≤
      ((sortedIntegerMaximum
        (inner.map (fun cell => (cell.upper, 209 * (cell.right - cell.left))) ++
          outer.map (fun cell => (cell.upper, 791 * (cell.right - cell.left))))).2 : ℝ) /
            ((D : ℝ) * (1000 * (K : ℝ)) ^ 2) := by
  let point (cells : List ContourGridCell) (i : ℕ) : ℤ :=
    (cells.getD i ⟨K, K, 0⟩).left
  let value (cells : List ContourGridCell) (i : ℕ) : ℤ :=
    (cells.getD i ⟨K, K, 0⟩).upper
  have hleft (cells : List ContourGridCell) (i : ℕ) (hi : i < cells.length) :
      point cells i = cells[i].left := by simp [point, hi]
  have hvalue (cells : List ContourGridCell) (i : ℕ) (hi : i < cells.length) :
      value cells i = cells[i].upper := by simp [value, hi]
  have hnext (cells : List ContourGridCell)
      (hc : cells.Chain' (fun c d => c.right = d.left))
      (hK : cells.getLast?.map ContourGridCell.right = some (K : ℤ))
      (i : ℕ) (hi : i < cells.length) : point cells (i + 1) = cells[i].right :=
    ContourGridCell.next_left_eq_right hc hK i hi
  have hfirst (cells : List ContourGridCell)
      (h0 : cells.head?.map ContourGridCell.left = some 0) : point cells 0 = 0 := by
    rcases Option.map_eq_some'.mp h0 with ⟨cell, hc, hcell⟩
    simpa [point, ← List.head?_eq_getElem?, hc] using hcell
  have hend (cells : List ContourGridCell) : point cells cells.length = K := by
    simp [point]
  have hmono (cells : List ContourGridCell)
      (hc : cells.Chain' (fun c d => c.right = d.left))
      (hK : cells.getLast?.map ContourGridCell.right = some (K : ℤ))
      (ho : ∀ cell ∈ cells, cell.left ≤ cell.right) :
      ∀ i < cells.length, point cells i ≤ point cells (i + 1) := by
    intro i hi
    rw [hleft cells i hi, hnext cells hc hK i hi]
    exact ho cells[i] (List.getElem_mem hi)
  have hinner : ∀ i < inner.length,
      ∀ x ∈ Set.Icc ((point inner i : ℝ) / K) ((point inner (i + 1) : ℝ) / K),
      circleLogProfile (fun z => cdtContourMap ((Real.exp (-1 / 2) : ℂ) * z)) x ≤
        (value inner i : ℝ) / D := by
    intro i hi x hx
    rw [hvalue inner i hi]
    have hx' : x ∈ Set.Icc ((inner[i].left : ℝ) / K) ((inner[i].right : ℝ) / K) := by
      simpa only [hleft inner i hi, hnext inner hichain hiK i hi] using hx
    exact hibound inner[i] (List.getElem_mem hi) x hx'
  have houter : ∀ i < outer.length,
      ∀ x ∈ Set.Icc ((point outer i : ℝ) / K) ((point outer (i + 1) : ℝ) / K),
      circleLogProfile cdtContourMap x ≤ (value outer i : ℝ) / D := by
    intro i hi x hx
    rw [hvalue outer i hi]
    have hx' : x ∈ Set.Icc ((outer[i].left : ℝ) / K) ((outer[i].right : ℝ) / K) := by
      simpa only [hleft outer i hi, hnext outer hochain hoK i hi] using hx
    simpa [ContourGridCell.Bounded] using hobound outer[i] (List.getElem_mem hi) x hx'
  have hf := continuous_circleLogProfile_cdtContourMap (Real.exp_pos (-1 / 2))
    (Real.exp_le_one_iff.mpr (by norm_num))
  have hg : Continuous (circleLogProfile cdtContourMap) := by
    simpa only [Complex.ofReal_one, one_mul] using
      continuous_circleLogProfile_cdtContourMap (r := 1) (by norm_num) le_rfl
  have hentries (cells : List ContourGridCell)
      (hc : cells.Chain' (fun c d => c.right = d.left))
      (hK : cells.getLast?.map ContourGridCell.right = some (K : ℤ)) (weight : ℤ) :
      List.ofFn (fun i : Fin cells.length =>
        (value cells i.1, weight * (point cells (i.1 + 1) - point cells i.1))) =
          cells.map (fun cell => (cell.upper, weight * (cell.right - cell.left))) := by
    rw [← List.ofFn_getElem_eq_map]
    apply congrArg List.ofFn
    funext i
    rw [hvalue cells i.1 i.isLt, hnext cells hc hK i.1 i.isLt, hleft cells i.1 i.isLt]
  have hbound := twoRadiusMaxIntegral_le_sortedGridCellSum cdtContourMap
    (Real.exp (-1 / 2)) hD hK hf hg (point inner) (point outer) (value inner) (value outer)
    (hfirst inner hi0) (hend inner) (hfirst outer ho0) (hend outer)
    (hmono inner hichain hiK hiorder) (hmono outer hochain hoK hoorder) hinner houter
  rw [hentries inner hichain hiK 209, hentries outer hochain hoK 791] at hbound
  exact hbound

end DirichletL
