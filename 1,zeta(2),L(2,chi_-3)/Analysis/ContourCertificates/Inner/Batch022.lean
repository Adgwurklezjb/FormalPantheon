import Analysis.ContourCertificates.Inner.Block0176
import Analysis.ContourCertificates.Inner.Block0177
import Analysis.ContourCertificates.Inner.Block0178
import Analysis.ContourCertificates.Inner.Block0179
import Analysis.ContourCertificates.Inner.Block0180
import Analysis.ContourCertificates.Inner.Block0181
import Analysis.ContourCertificates.Inner.Block0182
import Analysis.ContourCertificates.Inner.Block0183

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch022

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0176.cells ++
  DirichletL.ContourCertificates.Inner.Block0177.cells ++
  DirichletL.ContourCertificates.Inner.Block0178.cells ++
  DirichletL.ContourCertificates.Inner.Block0179.cells ++
  DirichletL.ContourCertificates.Inner.Block0180.cells ++
  DirichletL.ContourCertificates.Inner.Block0181.cells ++
  DirichletL.ContourCertificates.Inner.Block0182.cells ++
  DirichletL.ContourCertificates.Inner.Block0183.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0176.cells_bounded, DirichletL.ContourCertificates.Inner.Block0177.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0178.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0179.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0180.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0181.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0182.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0183.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch022
