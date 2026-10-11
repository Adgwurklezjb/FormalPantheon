import Analysis.ContourCertificates.Outer.Block1552
import Analysis.ContourCertificates.Outer.Block1553
import Analysis.ContourCertificates.Outer.Block1554
import Analysis.ContourCertificates.Outer.Block1555
import Analysis.ContourCertificates.Outer.Block1556
import Analysis.ContourCertificates.Outer.Block1557
import Analysis.ContourCertificates.Outer.Block1558
import Analysis.ContourCertificates.Outer.Block1559

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch194

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1552.cells ++
  DirichletL.ContourCertificates.Outer.Block1553.cells ++
  DirichletL.ContourCertificates.Outer.Block1554.cells ++
  DirichletL.ContourCertificates.Outer.Block1555.cells ++
  DirichletL.ContourCertificates.Outer.Block1556.cells ++
  DirichletL.ContourCertificates.Outer.Block1557.cells ++
  DirichletL.ContourCertificates.Outer.Block1558.cells ++
  DirichletL.ContourCertificates.Outer.Block1559.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1552.cells_bounded, DirichletL.ContourCertificates.Outer.Block1553.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1554.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1555.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1556.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1557.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1558.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1559.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch194
