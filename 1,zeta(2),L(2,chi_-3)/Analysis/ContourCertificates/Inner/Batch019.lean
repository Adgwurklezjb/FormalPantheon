import Analysis.ContourCertificates.Inner.Block0152
import Analysis.ContourCertificates.Inner.Block0153
import Analysis.ContourCertificates.Inner.Block0154
import Analysis.ContourCertificates.Inner.Block0155
import Analysis.ContourCertificates.Inner.Block0156
import Analysis.ContourCertificates.Inner.Block0157
import Analysis.ContourCertificates.Inner.Block0158
import Analysis.ContourCertificates.Inner.Block0159

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch019

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0152.cells ++
  DirichletL.ContourCertificates.Inner.Block0153.cells ++
  DirichletL.ContourCertificates.Inner.Block0154.cells ++
  DirichletL.ContourCertificates.Inner.Block0155.cells ++
  DirichletL.ContourCertificates.Inner.Block0156.cells ++
  DirichletL.ContourCertificates.Inner.Block0157.cells ++
  DirichletL.ContourCertificates.Inner.Block0158.cells ++
  DirichletL.ContourCertificates.Inner.Block0159.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0152.cells_bounded, DirichletL.ContourCertificates.Inner.Block0153.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0154.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0155.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0156.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0157.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0158.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0159.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch019
