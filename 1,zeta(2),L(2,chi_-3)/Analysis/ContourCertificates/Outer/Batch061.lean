import Analysis.ContourCertificates.Outer.Block0488
import Analysis.ContourCertificates.Outer.Block0489
import Analysis.ContourCertificates.Outer.Block0490
import Analysis.ContourCertificates.Outer.Block0491
import Analysis.ContourCertificates.Outer.Block0492
import Analysis.ContourCertificates.Outer.Block0493
import Analysis.ContourCertificates.Outer.Block0494
import Analysis.ContourCertificates.Outer.Block0495

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch061

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0488.cells ++
  DirichletL.ContourCertificates.Outer.Block0489.cells ++
  DirichletL.ContourCertificates.Outer.Block0490.cells ++
  DirichletL.ContourCertificates.Outer.Block0491.cells ++
  DirichletL.ContourCertificates.Outer.Block0492.cells ++
  DirichletL.ContourCertificates.Outer.Block0493.cells ++
  DirichletL.ContourCertificates.Outer.Block0494.cells ++
  DirichletL.ContourCertificates.Outer.Block0495.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0488.cells_bounded, DirichletL.ContourCertificates.Outer.Block0489.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0490.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0491.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0492.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0493.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0494.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0495.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch061
