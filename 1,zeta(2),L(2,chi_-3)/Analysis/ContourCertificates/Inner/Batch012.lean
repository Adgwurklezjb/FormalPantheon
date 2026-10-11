import Analysis.ContourCertificates.Inner.Block0096
import Analysis.ContourCertificates.Inner.Block0097
import Analysis.ContourCertificates.Inner.Block0098
import Analysis.ContourCertificates.Inner.Block0099
import Analysis.ContourCertificates.Inner.Block0100
import Analysis.ContourCertificates.Inner.Block0101
import Analysis.ContourCertificates.Inner.Block0102
import Analysis.ContourCertificates.Inner.Block0103

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch012

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0096.cells ++
  DirichletL.ContourCertificates.Inner.Block0097.cells ++
  DirichletL.ContourCertificates.Inner.Block0098.cells ++
  DirichletL.ContourCertificates.Inner.Block0099.cells ++
  DirichletL.ContourCertificates.Inner.Block0100.cells ++
  DirichletL.ContourCertificates.Inner.Block0101.cells ++
  DirichletL.ContourCertificates.Inner.Block0102.cells ++
  DirichletL.ContourCertificates.Inner.Block0103.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0096.cells_bounded, DirichletL.ContourCertificates.Inner.Block0097.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0098.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0099.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0100.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0101.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0102.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0103.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch012
