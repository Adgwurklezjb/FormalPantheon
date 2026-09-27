import Analysis.ContourGridCell

/-!
List endpoints for CDT's contour partition, author page 174; supplied TeX 8384–8404.
Meanings and terminal-index checks precede this body in
-/

namespace DirichletL.ContourGridCell

theorem next_left_eq_right {cells : List ContourGridCell} {K : ℤ}
    (hchain : cells.Chain' (fun c d => c.right = d.left))
    (hlast : cells.getLast?.map ContourGridCell.right = some K)
    (i : ℕ) (hi : i < cells.length) :
    (cells.getD (i + 1) ⟨K, K, 0⟩).left = cells[i].right := by
  by_cases hn : i + 1 < cells.length
  · have hc := List.chain'_iff_get.mp hchain i (by omega)
    simpa [List.getD_eq_getElem?_getD, hn] using hc.symm
  · have hidx : cells.length - 1 = i := by omega
    have hlast' : cells[i].right = K := by
      simpa [List.getLast?_eq_getElem?, hidx, hi] using hlast
    have hle : cells.length ≤ i + 1 := by omega
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle] using hlast'.symm

end DirichletL.ContourGridCell
