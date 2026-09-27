import Analysis.ContourCertificates.Inner.Block0320
import Analysis.ContourCertificates.Inner.Block0321
import Analysis.ContourCertificates.Inner.Block0322
import Analysis.ContourCertificates.Inner.Block0323
import Analysis.ContourCertificates.Inner.Block0324
import Analysis.ContourCertificates.Inner.Block0325
import Analysis.ContourCertificates.Inner.Block0326
import Analysis.ContourCertificates.Inner.Block0327

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch040

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0320.cells ++
  DirichletL.ContourCertificates.Inner.Block0321.cells ++
  DirichletL.ContourCertificates.Inner.Block0322.cells ++
  DirichletL.ContourCertificates.Inner.Block0323.cells ++
  DirichletL.ContourCertificates.Inner.Block0324.cells ++
  DirichletL.ContourCertificates.Inner.Block0325.cells ++
  DirichletL.ContourCertificates.Inner.Block0326.cells ++
  DirichletL.ContourCertificates.Inner.Block0327.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0320.cells_bounded, DirichletL.ContourCertificates.Inner.Block0321.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0322.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0323.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0324.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0325.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0326.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0327.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch040
