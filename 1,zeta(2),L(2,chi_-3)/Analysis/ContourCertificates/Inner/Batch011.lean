import Analysis.ContourCertificates.Inner.Block0088
import Analysis.ContourCertificates.Inner.Block0089
import Analysis.ContourCertificates.Inner.Block0090
import Analysis.ContourCertificates.Inner.Block0091
import Analysis.ContourCertificates.Inner.Block0092
import Analysis.ContourCertificates.Inner.Block0093
import Analysis.ContourCertificates.Inner.Block0094
import Analysis.ContourCertificates.Inner.Block0095

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch011

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0088.cells ++
  DirichletL.ContourCertificates.Inner.Block0089.cells ++
  DirichletL.ContourCertificates.Inner.Block0090.cells ++
  DirichletL.ContourCertificates.Inner.Block0091.cells ++
  DirichletL.ContourCertificates.Inner.Block0092.cells ++
  DirichletL.ContourCertificates.Inner.Block0093.cells ++
  DirichletL.ContourCertificates.Inner.Block0094.cells ++
  DirichletL.ContourCertificates.Inner.Block0095.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0088.cells_bounded, DirichletL.ContourCertificates.Inner.Block0089.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0090.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0091.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0092.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0093.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0094.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0095.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch011
