import Analysis.ContourCertificates.Outer.Block1432
import Analysis.ContourCertificates.Outer.Block1433
import Analysis.ContourCertificates.Outer.Block1434
import Analysis.ContourCertificates.Outer.Block1435
import Analysis.ContourCertificates.Outer.Block1436
import Analysis.ContourCertificates.Outer.Block1437
import Analysis.ContourCertificates.Outer.Block1438
import Analysis.ContourCertificates.Outer.Block1439

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch179

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1432.cells ++
  DirichletL.ContourCertificates.Outer.Block1433.cells ++
  DirichletL.ContourCertificates.Outer.Block1434.cells ++
  DirichletL.ContourCertificates.Outer.Block1435.cells ++
  DirichletL.ContourCertificates.Outer.Block1436.cells ++
  DirichletL.ContourCertificates.Outer.Block1437.cells ++
  DirichletL.ContourCertificates.Outer.Block1438.cells ++
  DirichletL.ContourCertificates.Outer.Block1439.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1432.cells_bounded, DirichletL.ContourCertificates.Outer.Block1433.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1434.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1435.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1436.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1437.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1438.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1439.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch179
