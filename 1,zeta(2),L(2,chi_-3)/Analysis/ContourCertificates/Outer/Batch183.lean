import Analysis.ContourCertificates.Outer.Block1464
import Analysis.ContourCertificates.Outer.Block1465
import Analysis.ContourCertificates.Outer.Block1466
import Analysis.ContourCertificates.Outer.Block1467
import Analysis.ContourCertificates.Outer.Block1468
import Analysis.ContourCertificates.Outer.Block1469
import Analysis.ContourCertificates.Outer.Block1470
import Analysis.ContourCertificates.Outer.Block1471

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch183

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1464.cells ++
  DirichletL.ContourCertificates.Outer.Block1465.cells ++
  DirichletL.ContourCertificates.Outer.Block1466.cells ++
  DirichletL.ContourCertificates.Outer.Block1467.cells ++
  DirichletL.ContourCertificates.Outer.Block1468.cells ++
  DirichletL.ContourCertificates.Outer.Block1469.cells ++
  DirichletL.ContourCertificates.Outer.Block1470.cells ++
  DirichletL.ContourCertificates.Outer.Block1471.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1464.cells_bounded, DirichletL.ContourCertificates.Outer.Block1465.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1466.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1467.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1468.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1469.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1470.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1471.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch183
