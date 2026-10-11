import Analysis.ContourCertificates.Inner.Block0104
import Analysis.ContourCertificates.Inner.Block0105
import Analysis.ContourCertificates.Inner.Block0106
import Analysis.ContourCertificates.Inner.Block0107
import Analysis.ContourCertificates.Inner.Block0108
import Analysis.ContourCertificates.Inner.Block0109
import Analysis.ContourCertificates.Inner.Block0110
import Analysis.ContourCertificates.Inner.Block0111

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch013

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0104.cells ++
  DirichletL.ContourCertificates.Inner.Block0105.cells ++
  DirichletL.ContourCertificates.Inner.Block0106.cells ++
  DirichletL.ContourCertificates.Inner.Block0107.cells ++
  DirichletL.ContourCertificates.Inner.Block0108.cells ++
  DirichletL.ContourCertificates.Inner.Block0109.cells ++
  DirichletL.ContourCertificates.Inner.Block0110.cells ++
  DirichletL.ContourCertificates.Inner.Block0111.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0104.cells_bounded, DirichletL.ContourCertificates.Inner.Block0105.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0106.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0107.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0108.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0109.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0110.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0111.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch013
