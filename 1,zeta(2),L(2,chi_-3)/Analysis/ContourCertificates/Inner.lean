import Analysis.ContourCertificates.Inner.Batch000
import Analysis.ContourCertificates.Inner.Batch001
import Analysis.ContourCertificates.Inner.Batch002
import Analysis.ContourCertificates.Inner.Batch003
import Analysis.ContourCertificates.Inner.Batch004
import Analysis.ContourCertificates.Inner.Batch005
import Analysis.ContourCertificates.Inner.Batch006
import Analysis.ContourCertificates.Inner.Batch007
import Analysis.ContourCertificates.Inner.Batch008
import Analysis.ContourCertificates.Inner.Batch009
import Analysis.ContourCertificates.Inner.Batch010
import Analysis.ContourCertificates.Inner.Batch011
import Analysis.ContourCertificates.Inner.Batch012
import Analysis.ContourCertificates.Inner.Batch013
import Analysis.ContourCertificates.Inner.Batch014
import Analysis.ContourCertificates.Inner.Batch015
import Analysis.ContourCertificates.Inner.Batch016
import Analysis.ContourCertificates.Inner.Batch017
import Analysis.ContourCertificates.Inner.Batch018
import Analysis.ContourCertificates.Inner.Batch019
import Analysis.ContourCertificates.Inner.Batch020
import Analysis.ContourCertificates.Inner.Batch021
import Analysis.ContourCertificates.Inner.Batch022
import Analysis.ContourCertificates.Inner.Batch023
import Analysis.ContourCertificates.Inner.Batch024
import Analysis.ContourCertificates.Inner.Batch025
import Analysis.ContourCertificates.Inner.Batch026
import Analysis.ContourCertificates.Inner.Batch027
import Analysis.ContourCertificates.Inner.Batch028
import Analysis.ContourCertificates.Inner.Batch029
import Analysis.ContourCertificates.Inner.Batch030
import Analysis.ContourCertificates.Inner.Batch031
import Analysis.ContourCertificates.Inner.Batch032
import Analysis.ContourCertificates.Inner.Batch033
import Analysis.ContourCertificates.Inner.Batch034
import Analysis.ContourCertificates.Inner.Batch035
import Analysis.ContourCertificates.Inner.Batch036
import Analysis.ContourCertificates.Inner.Batch037
import Analysis.ContourCertificates.Inner.Batch038
import Analysis.ContourCertificates.Inner.Batch039
import Analysis.ContourCertificates.Inner.Batch040
import Analysis.ContourCertificates.Inner.Batch041

/-!
Complete inner grid partition for CDT's signed two-radius bound.
Source: corrected author page 174 and Appendix A.4, page 204;
supplied v2 TeX 3503-3538 and 8384-8404.
-/

namespace DirichletL.ContourCertificates.Inner

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All existing inner cells, preserving their order and signed bound/interval pairing. -/
def cells : List ContourGridCell := Batch000.cells ++
  Batch001.cells ++
  Batch002.cells ++
  Batch003.cells ++
  Batch004.cells ++
  Batch005.cells ++
  Batch006.cells ++
  Batch007.cells ++
  Batch008.cells ++
  Batch009.cells ++
  Batch010.cells ++
  Batch011.cells ++
  Batch012.cells ++
  Batch013.cells ++
  Batch014.cells ++
  Batch015.cells ++
  Batch016.cells ++
  Batch017.cells ++
  Batch018.cells ++
  Batch019.cells ++
  Batch020.cells ++
  Batch021.cells ++
  Batch022.cells ++
  Batch023.cells ++
  Batch024.cells ++
  Batch025.cells ++
  Batch026.cells ++
  Batch027.cells ++
  Batch028.cells ++
  Batch029.cells ++
  Batch030.cells ++
  Batch031.cells ++
  Batch032.cells ++
  Batch033.cells ++
  Batch034.cells ++
  Batch035.cells ++
  Batch036.cells ++
  Batch037.cells ++
  Batch038.cells ++
  Batch039.cells ++
  Batch040.cells ++
  Batch041.cells

theorem cells_length : cells.length = 661 := by decide +kernel

theorem cells_head_left : cells.head?.map ContourGridCell.left = some 0 := by decide +kernel

theorem cells_last_right : cells.getLast?.map ContourGridCell.right = some 65536 := by decide +kernel

theorem cells_chain : cells.IsChain (fun c d => c.right = d.left) := by decide +kernel

theorem cells_order : ∀ cell ∈ cells, cell.left ≤ cell.right := by decide +kernel

theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  refine ⟨?_, Batch041.cells_bounded⟩
  refine ⟨?_, Batch040.cells_bounded⟩
  refine ⟨?_, Batch039.cells_bounded⟩
  refine ⟨?_, Batch038.cells_bounded⟩
  refine ⟨?_, Batch037.cells_bounded⟩
  refine ⟨?_, Batch036.cells_bounded⟩
  refine ⟨?_, Batch035.cells_bounded⟩
  refine ⟨?_, Batch034.cells_bounded⟩
  refine ⟨?_, Batch033.cells_bounded⟩
  refine ⟨?_, Batch032.cells_bounded⟩
  refine ⟨?_, Batch031.cells_bounded⟩
  refine ⟨?_, Batch030.cells_bounded⟩
  refine ⟨?_, Batch029.cells_bounded⟩
  refine ⟨?_, Batch028.cells_bounded⟩
  refine ⟨?_, Batch027.cells_bounded⟩
  refine ⟨?_, Batch026.cells_bounded⟩
  refine ⟨?_, Batch025.cells_bounded⟩
  refine ⟨?_, Batch024.cells_bounded⟩
  refine ⟨?_, Batch023.cells_bounded⟩
  refine ⟨?_, Batch022.cells_bounded⟩
  refine ⟨?_, Batch021.cells_bounded⟩
  refine ⟨?_, Batch020.cells_bounded⟩
  refine ⟨?_, Batch019.cells_bounded⟩
  refine ⟨?_, Batch018.cells_bounded⟩
  refine ⟨?_, Batch017.cells_bounded⟩
  refine ⟨?_, Batch016.cells_bounded⟩
  refine ⟨?_, Batch015.cells_bounded⟩
  refine ⟨?_, Batch014.cells_bounded⟩
  refine ⟨?_, Batch013.cells_bounded⟩
  refine ⟨?_, Batch012.cells_bounded⟩
  refine ⟨?_, Batch011.cells_bounded⟩
  refine ⟨?_, Batch010.cells_bounded⟩
  refine ⟨?_, Batch009.cells_bounded⟩
  refine ⟨?_, Batch008.cells_bounded⟩
  refine ⟨?_, Batch007.cells_bounded⟩
  refine ⟨?_, Batch006.cells_bounded⟩
  refine ⟨?_, Batch005.cells_bounded⟩
  refine ⟨?_, Batch004.cells_bounded⟩
  refine ⟨?_, Batch003.cells_bounded⟩
  refine ⟨?_, Batch002.cells_bounded⟩
  refine ⟨?_, Batch001.cells_bounded⟩
  exact Batch000.cells_bounded

end DirichletL.ContourCertificates.Inner
