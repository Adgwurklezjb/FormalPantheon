import Analysis.ContourCertificates.Outer.Block0704
import Analysis.ContourCertificates.Outer.Block0705
import Analysis.ContourCertificates.Outer.Block0706
import Analysis.ContourCertificates.Outer.Block0707
import Analysis.ContourCertificates.Outer.Block0708
import Analysis.ContourCertificates.Outer.Block0709
import Analysis.ContourCertificates.Outer.Block0710
import Analysis.ContourCertificates.Outer.Block0711

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch088

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0704.cells ++
  DirichletL.ContourCertificates.Outer.Block0705.cells ++
  DirichletL.ContourCertificates.Outer.Block0706.cells ++
  DirichletL.ContourCertificates.Outer.Block0707.cells ++
  DirichletL.ContourCertificates.Outer.Block0708.cells ++
  DirichletL.ContourCertificates.Outer.Block0709.cells ++
  DirichletL.ContourCertificates.Outer.Block0710.cells ++
  DirichletL.ContourCertificates.Outer.Block0711.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0704.cells_bounded, DirichletL.ContourCertificates.Outer.Block0705.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0706.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0707.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0708.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0709.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0710.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0711.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch088
