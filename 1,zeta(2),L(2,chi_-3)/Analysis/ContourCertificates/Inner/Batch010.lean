import Analysis.ContourCertificates.Inner.Block0080
import Analysis.ContourCertificates.Inner.Block0081
import Analysis.ContourCertificates.Inner.Block0082
import Analysis.ContourCertificates.Inner.Block0083
import Analysis.ContourCertificates.Inner.Block0084
import Analysis.ContourCertificates.Inner.Block0085
import Analysis.ContourCertificates.Inner.Block0086
import Analysis.ContourCertificates.Inner.Block0087

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch010

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0080.cells ++
  DirichletL.ContourCertificates.Inner.Block0081.cells ++
  DirichletL.ContourCertificates.Inner.Block0082.cells ++
  DirichletL.ContourCertificates.Inner.Block0083.cells ++
  DirichletL.ContourCertificates.Inner.Block0084.cells ++
  DirichletL.ContourCertificates.Inner.Block0085.cells ++
  DirichletL.ContourCertificates.Inner.Block0086.cells ++
  DirichletL.ContourCertificates.Inner.Block0087.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0080.cells_bounded, DirichletL.ContourCertificates.Inner.Block0081.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0082.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0083.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0084.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0085.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0086.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0087.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch010
