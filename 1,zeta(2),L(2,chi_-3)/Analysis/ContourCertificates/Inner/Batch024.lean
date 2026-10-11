import Analysis.ContourCertificates.Inner.Block0192
import Analysis.ContourCertificates.Inner.Block0193
import Analysis.ContourCertificates.Inner.Block0194
import Analysis.ContourCertificates.Inner.Block0195
import Analysis.ContourCertificates.Inner.Block0196
import Analysis.ContourCertificates.Inner.Block0197
import Analysis.ContourCertificates.Inner.Block0198
import Analysis.ContourCertificates.Inner.Block0199

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch024

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0192.cells ++
  DirichletL.ContourCertificates.Inner.Block0193.cells ++
  DirichletL.ContourCertificates.Inner.Block0194.cells ++
  DirichletL.ContourCertificates.Inner.Block0195.cells ++
  DirichletL.ContourCertificates.Inner.Block0196.cells ++
  DirichletL.ContourCertificates.Inner.Block0197.cells ++
  DirichletL.ContourCertificates.Inner.Block0198.cells ++
  DirichletL.ContourCertificates.Inner.Block0199.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0192.cells_bounded, DirichletL.ContourCertificates.Inner.Block0193.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0194.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0195.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0196.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0197.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0198.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0199.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch024
