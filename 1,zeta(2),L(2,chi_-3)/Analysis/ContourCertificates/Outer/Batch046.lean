import Analysis.ContourCertificates.Outer.Block0368
import Analysis.ContourCertificates.Outer.Block0369
import Analysis.ContourCertificates.Outer.Block0370
import Analysis.ContourCertificates.Outer.Block0371
import Analysis.ContourCertificates.Outer.Block0372
import Analysis.ContourCertificates.Outer.Block0373
import Analysis.ContourCertificates.Outer.Block0374
import Analysis.ContourCertificates.Outer.Block0375

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch046

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0368.cells ++
  DirichletL.ContourCertificates.Outer.Block0369.cells ++
  DirichletL.ContourCertificates.Outer.Block0370.cells ++
  DirichletL.ContourCertificates.Outer.Block0371.cells ++
  DirichletL.ContourCertificates.Outer.Block0372.cells ++
  DirichletL.ContourCertificates.Outer.Block0373.cells ++
  DirichletL.ContourCertificates.Outer.Block0374.cells ++
  DirichletL.ContourCertificates.Outer.Block0375.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0368.cells_bounded, DirichletL.ContourCertificates.Outer.Block0369.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0370.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0371.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0372.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0373.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0374.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0375.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch046
