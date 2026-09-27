import Analysis.ContourCertificates.Inner.Block0136
import Analysis.ContourCertificates.Inner.Block0137
import Analysis.ContourCertificates.Inner.Block0138
import Analysis.ContourCertificates.Inner.Block0139
import Analysis.ContourCertificates.Inner.Block0140
import Analysis.ContourCertificates.Inner.Block0141
import Analysis.ContourCertificates.Inner.Block0142
import Analysis.ContourCertificates.Inner.Block0143

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch017

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0136.cells ++
  DirichletL.ContourCertificates.Inner.Block0137.cells ++
  DirichletL.ContourCertificates.Inner.Block0138.cells ++
  DirichletL.ContourCertificates.Inner.Block0139.cells ++
  DirichletL.ContourCertificates.Inner.Block0140.cells ++
  DirichletL.ContourCertificates.Inner.Block0141.cells ++
  DirichletL.ContourCertificates.Inner.Block0142.cells ++
  DirichletL.ContourCertificates.Inner.Block0143.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0136.cells_bounded, DirichletL.ContourCertificates.Inner.Block0137.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0138.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0139.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0140.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0141.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0142.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0143.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch017
