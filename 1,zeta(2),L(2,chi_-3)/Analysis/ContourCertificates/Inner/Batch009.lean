import Analysis.ContourCertificates.Inner.Block0072
import Analysis.ContourCertificates.Inner.Block0073
import Analysis.ContourCertificates.Inner.Block0074
import Analysis.ContourCertificates.Inner.Block0075
import Analysis.ContourCertificates.Inner.Block0076
import Analysis.ContourCertificates.Inner.Block0077
import Analysis.ContourCertificates.Inner.Block0078
import Analysis.ContourCertificates.Inner.Block0079

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch009

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0072.cells ++
  DirichletL.ContourCertificates.Inner.Block0073.cells ++
  DirichletL.ContourCertificates.Inner.Block0074.cells ++
  DirichletL.ContourCertificates.Inner.Block0075.cells ++
  DirichletL.ContourCertificates.Inner.Block0076.cells ++
  DirichletL.ContourCertificates.Inner.Block0077.cells ++
  DirichletL.ContourCertificates.Inner.Block0078.cells ++
  DirichletL.ContourCertificates.Inner.Block0079.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0072.cells_bounded, DirichletL.ContourCertificates.Inner.Block0073.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0074.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0075.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0076.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0077.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0078.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0079.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch009
