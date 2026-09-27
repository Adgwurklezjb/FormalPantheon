import Analysis.ContourCertificates.Inner.Block0304
import Analysis.ContourCertificates.Inner.Block0305
import Analysis.ContourCertificates.Inner.Block0306
import Analysis.ContourCertificates.Inner.Block0307
import Analysis.ContourCertificates.Inner.Block0308
import Analysis.ContourCertificates.Inner.Block0309
import Analysis.ContourCertificates.Inner.Block0310
import Analysis.ContourCertificates.Inner.Block0311

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch038

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0304.cells ++
  DirichletL.ContourCertificates.Inner.Block0305.cells ++
  DirichletL.ContourCertificates.Inner.Block0306.cells ++
  DirichletL.ContourCertificates.Inner.Block0307.cells ++
  DirichletL.ContourCertificates.Inner.Block0308.cells ++
  DirichletL.ContourCertificates.Inner.Block0309.cells ++
  DirichletL.ContourCertificates.Inner.Block0310.cells ++
  DirichletL.ContourCertificates.Inner.Block0311.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0304.cells_bounded, DirichletL.ContourCertificates.Inner.Block0305.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0306.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0307.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0308.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0309.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0310.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0311.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch038
