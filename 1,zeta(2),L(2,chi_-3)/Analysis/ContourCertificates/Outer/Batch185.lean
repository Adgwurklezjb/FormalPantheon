import Analysis.ContourCertificates.Outer.Block1480
import Analysis.ContourCertificates.Outer.Block1481
import Analysis.ContourCertificates.Outer.Block1482
import Analysis.ContourCertificates.Outer.Block1483
import Analysis.ContourCertificates.Outer.Block1484
import Analysis.ContourCertificates.Outer.Block1485
import Analysis.ContourCertificates.Outer.Block1486
import Analysis.ContourCertificates.Outer.Block1487

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch185

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1480.cells ++
  DirichletL.ContourCertificates.Outer.Block1481.cells ++
  DirichletL.ContourCertificates.Outer.Block1482.cells ++
  DirichletL.ContourCertificates.Outer.Block1483.cells ++
  DirichletL.ContourCertificates.Outer.Block1484.cells ++
  DirichletL.ContourCertificates.Outer.Block1485.cells ++
  DirichletL.ContourCertificates.Outer.Block1486.cells ++
  DirichletL.ContourCertificates.Outer.Block1487.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1480.cells_bounded, DirichletL.ContourCertificates.Outer.Block1481.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1482.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1483.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1484.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1485.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1486.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1487.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch185
