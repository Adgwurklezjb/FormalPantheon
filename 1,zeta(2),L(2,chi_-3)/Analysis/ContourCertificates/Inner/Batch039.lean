import Analysis.ContourCertificates.Inner.Block0312
import Analysis.ContourCertificates.Inner.Block0313
import Analysis.ContourCertificates.Inner.Block0314
import Analysis.ContourCertificates.Inner.Block0315
import Analysis.ContourCertificates.Inner.Block0316
import Analysis.ContourCertificates.Inner.Block0317
import Analysis.ContourCertificates.Inner.Block0318
import Analysis.ContourCertificates.Inner.Block0319

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch039

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0312.cells ++
  DirichletL.ContourCertificates.Inner.Block0313.cells ++
  DirichletL.ContourCertificates.Inner.Block0314.cells ++
  DirichletL.ContourCertificates.Inner.Block0315.cells ++
  DirichletL.ContourCertificates.Inner.Block0316.cells ++
  DirichletL.ContourCertificates.Inner.Block0317.cells ++
  DirichletL.ContourCertificates.Inner.Block0318.cells ++
  DirichletL.ContourCertificates.Inner.Block0319.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0312.cells_bounded, DirichletL.ContourCertificates.Inner.Block0313.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0314.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0315.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0316.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0317.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0318.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0319.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch039
