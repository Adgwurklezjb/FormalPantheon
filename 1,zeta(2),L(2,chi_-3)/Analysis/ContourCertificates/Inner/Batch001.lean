import Analysis.ContourCertificates.Inner.Block0008
import Analysis.ContourCertificates.Inner.Block0009
import Analysis.ContourCertificates.Inner.Block0010
import Analysis.ContourCertificates.Inner.Block0011
import Analysis.ContourCertificates.Inner.Block0012
import Analysis.ContourCertificates.Inner.Block0013
import Analysis.ContourCertificates.Inner.Block0014
import Analysis.ContourCertificates.Inner.Block0015

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch001

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0008.cells ++
  DirichletL.ContourCertificates.Inner.Block0009.cells ++
  DirichletL.ContourCertificates.Inner.Block0010.cells ++
  DirichletL.ContourCertificates.Inner.Block0011.cells ++
  DirichletL.ContourCertificates.Inner.Block0012.cells ++
  DirichletL.ContourCertificates.Inner.Block0013.cells ++
  DirichletL.ContourCertificates.Inner.Block0014.cells ++
  DirichletL.ContourCertificates.Inner.Block0015.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0008.cells_bounded, DirichletL.ContourCertificates.Inner.Block0009.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0010.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0011.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0012.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0013.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0014.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0015.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch001
