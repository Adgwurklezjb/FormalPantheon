import Analysis.ContourCertificates.Outer.Block0392
import Analysis.ContourCertificates.Outer.Block0393
import Analysis.ContourCertificates.Outer.Block0394
import Analysis.ContourCertificates.Outer.Block0395
import Analysis.ContourCertificates.Outer.Block0396
import Analysis.ContourCertificates.Outer.Block0397
import Analysis.ContourCertificates.Outer.Block0398
import Analysis.ContourCertificates.Outer.Block0399

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch049

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0392.cells ++
  DirichletL.ContourCertificates.Outer.Block0393.cells ++
  DirichletL.ContourCertificates.Outer.Block0394.cells ++
  DirichletL.ContourCertificates.Outer.Block0395.cells ++
  DirichletL.ContourCertificates.Outer.Block0396.cells ++
  DirichletL.ContourCertificates.Outer.Block0397.cells ++
  DirichletL.ContourCertificates.Outer.Block0398.cells ++
  DirichletL.ContourCertificates.Outer.Block0399.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0392.cells_bounded, DirichletL.ContourCertificates.Outer.Block0393.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0394.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0395.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0396.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0397.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0398.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0399.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch049
