import Analysis.ContourCertificates.Outer.Block1544
import Analysis.ContourCertificates.Outer.Block1545
import Analysis.ContourCertificates.Outer.Block1546
import Analysis.ContourCertificates.Outer.Block1547
import Analysis.ContourCertificates.Outer.Block1548
import Analysis.ContourCertificates.Outer.Block1549
import Analysis.ContourCertificates.Outer.Block1550
import Analysis.ContourCertificates.Outer.Block1551

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch193

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1544.cells ++
  DirichletL.ContourCertificates.Outer.Block1545.cells ++
  DirichletL.ContourCertificates.Outer.Block1546.cells ++
  DirichletL.ContourCertificates.Outer.Block1547.cells ++
  DirichletL.ContourCertificates.Outer.Block1548.cells ++
  DirichletL.ContourCertificates.Outer.Block1549.cells ++
  DirichletL.ContourCertificates.Outer.Block1550.cells ++
  DirichletL.ContourCertificates.Outer.Block1551.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1544.cells_bounded, DirichletL.ContourCertificates.Outer.Block1545.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1546.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1547.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1548.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1549.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1550.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1551.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch193
