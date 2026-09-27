import Analysis.ContourCertificates.Inner.Block0040
import Analysis.ContourCertificates.Inner.Block0041
import Analysis.ContourCertificates.Inner.Block0042
import Analysis.ContourCertificates.Inner.Block0043
import Analysis.ContourCertificates.Inner.Block0044
import Analysis.ContourCertificates.Inner.Block0045
import Analysis.ContourCertificates.Inner.Block0046
import Analysis.ContourCertificates.Inner.Block0047

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch005

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0040.cells ++
  DirichletL.ContourCertificates.Inner.Block0041.cells ++
  DirichletL.ContourCertificates.Inner.Block0042.cells ++
  DirichletL.ContourCertificates.Inner.Block0043.cells ++
  DirichletL.ContourCertificates.Inner.Block0044.cells ++
  DirichletL.ContourCertificates.Inner.Block0045.cells ++
  DirichletL.ContourCertificates.Inner.Block0046.cells ++
  DirichletL.ContourCertificates.Inner.Block0047.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0040.cells_bounded, DirichletL.ContourCertificates.Inner.Block0041.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0042.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0043.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0044.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0045.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0046.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0047.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch005
