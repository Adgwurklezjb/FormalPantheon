import Analysis.ContourCertificates.Inner.Block0120
import Analysis.ContourCertificates.Inner.Block0121
import Analysis.ContourCertificates.Inner.Block0122
import Analysis.ContourCertificates.Inner.Block0123
import Analysis.ContourCertificates.Inner.Block0124
import Analysis.ContourCertificates.Inner.Block0125
import Analysis.ContourCertificates.Inner.Block0126
import Analysis.ContourCertificates.Inner.Block0127

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch015

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0120.cells ++
  DirichletL.ContourCertificates.Inner.Block0121.cells ++
  DirichletL.ContourCertificates.Inner.Block0122.cells ++
  DirichletL.ContourCertificates.Inner.Block0123.cells ++
  DirichletL.ContourCertificates.Inner.Block0124.cells ++
  DirichletL.ContourCertificates.Inner.Block0125.cells ++
  DirichletL.ContourCertificates.Inner.Block0126.cells ++
  DirichletL.ContourCertificates.Inner.Block0127.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0120.cells_bounded, DirichletL.ContourCertificates.Inner.Block0121.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0122.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0123.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0124.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0125.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0126.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0127.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch015
