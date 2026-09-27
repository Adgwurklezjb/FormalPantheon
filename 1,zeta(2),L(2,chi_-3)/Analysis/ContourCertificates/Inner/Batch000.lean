import Analysis.ContourCertificates.Inner.Block0000
import Analysis.ContourCertificates.Inner.Block0001
import Analysis.ContourCertificates.Inner.Block0002
import Analysis.ContourCertificates.Inner.Block0003
import Analysis.ContourCertificates.Inner.Block0004
import Analysis.ContourCertificates.Inner.Block0005
import Analysis.ContourCertificates.Inner.Block0006
import Analysis.ContourCertificates.Inner.Block0007

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch000

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0000.cells ++
  DirichletL.ContourCertificates.Inner.Block0001.cells ++
  DirichletL.ContourCertificates.Inner.Block0002.cells ++
  DirichletL.ContourCertificates.Inner.Block0003.cells ++
  DirichletL.ContourCertificates.Inner.Block0004.cells ++
  DirichletL.ContourCertificates.Inner.Block0005.cells ++
  DirichletL.ContourCertificates.Inner.Block0006.cells ++
  DirichletL.ContourCertificates.Inner.Block0007.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0000.cells_bounded, DirichletL.ContourCertificates.Inner.Block0001.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0002.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0003.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0004.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0005.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0006.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0007.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch000
