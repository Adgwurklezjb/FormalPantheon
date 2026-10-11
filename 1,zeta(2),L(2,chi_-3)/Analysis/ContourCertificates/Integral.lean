import Analysis.ContourCertificates.Inner
import Analysis.ContourCertificates.Outer
import Analysis.ContourCertificateIntegral
import Analysis.IntegerMaximumComputation

/-!
The exact signed contour numerator and the concrete bound 57/5.
Source: CDT author page 174 and Appendix A.4 page 204;
supplied v2 TeX 3503-3538 and 8384-8404.
-/

namespace DirichletL

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

theorem sortedIntegerMaximum_contourCells_snd :
    (sortedIntegerMaximum
      (ContourCertificates.Inner.cells.map (fun cell =>
        (cell.upper, 209 * (cell.right - cell.left))) ++
        ContourCertificates.Outer.cells.map (fun cell =>
          (cell.upper, 791 * (cell.right - cell.left))))).2 =
      65051948783694992222053224604406290310436692096922675 := by
  let entries : List (ℤ × ℤ) :=
    ContourCertificates.Inner.cells.map (fun cell =>
      (cell.upper, 209 * (cell.right - cell.left))) ++
      ContourCertificates.Outer.cells.map (fun cell =>
        (cell.upper, 791 * (cell.right - cell.left)))
  have hlength : entries.length ≤ 2 ^ 12 := by
    simp only [entries, List.length_append, List.length_map,
      ContourCertificates.Inner.cells_length, ContourCertificates.Outer.cells_length]
    norm_num
  change (sortedIntegerMaximum entries).2 = _
  rw [sortedIntegerMaximum_eq_fold_sortIntegerPairsWithFuel 12 entries hlength]
  dsimp only [entries]
  decide +kernel

theorem twoRadiusMaxIntegral_cdtContourMap_le :
    twoRadiusMaxIntegral cdtContourMap (Real.exp (-1 / 2)) (209 / 1000) ≤ 57 / 5 := by
  have hb := twoRadiusMaxIntegral_le_sortedContourCells
    (D := 2 ^ 120) (K := 65536) (by norm_num) (by norm_num)
    ContourCertificates.Inner.cells ContourCertificates.Outer.cells
    ContourCertificates.Inner.cells_head_left ContourCertificates.Inner.cells_last_right
    ContourCertificates.Outer.cells_head_left ContourCertificates.Outer.cells_last_right
    ContourCertificates.Inner.cells_chain ContourCertificates.Outer.cells_chain
    ContourCertificates.Inner.cells_order ContourCertificates.Outer.cells_order
    ContourCertificates.Inner.cells_bounded ContourCertificates.Outer.cells_bounded
  rw [sortedIntegerMaximum_contourCells_snd] at hb
  refine hb.trans ?_
  norm_num

end DirichletL
