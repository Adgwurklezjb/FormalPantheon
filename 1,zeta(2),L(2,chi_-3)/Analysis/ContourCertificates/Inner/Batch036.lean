import Analysis.ContourCertificates.Inner.Block0288
import Analysis.ContourCertificates.Inner.Block0289
import Analysis.ContourCertificates.Inner.Block0290
import Analysis.ContourCertificates.Inner.Block0291
import Analysis.ContourCertificates.Inner.Block0292
import Analysis.ContourCertificates.Inner.Block0293
import Analysis.ContourCertificates.Inner.Block0294
import Analysis.ContourCertificates.Inner.Block0295

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch036

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0288.cells ++
  DirichletL.ContourCertificates.Inner.Block0289.cells ++
  DirichletL.ContourCertificates.Inner.Block0290.cells ++
  DirichletL.ContourCertificates.Inner.Block0291.cells ++
  DirichletL.ContourCertificates.Inner.Block0292.cells ++
  DirichletL.ContourCertificates.Inner.Block0293.cells ++
  DirichletL.ContourCertificates.Inner.Block0294.cells ++
  DirichletL.ContourCertificates.Inner.Block0295.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0288.cells_bounded, DirichletL.ContourCertificates.Inner.Block0289.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0290.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0291.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0292.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0293.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0294.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0295.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch036
