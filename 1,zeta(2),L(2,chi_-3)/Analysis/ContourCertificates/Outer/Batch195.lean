import Analysis.ContourCertificates.Outer.Block1560
import Analysis.ContourCertificates.Outer.Block1561
import Analysis.ContourCertificates.Outer.Block1562
import Analysis.ContourCertificates.Outer.Block1563
import Analysis.ContourCertificates.Outer.Block1564
import Analysis.ContourCertificates.Outer.Block1565
import Analysis.ContourCertificates.Outer.Block1566
import Analysis.ContourCertificates.Outer.Block1567

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch195

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1560.cells ++
  DirichletL.ContourCertificates.Outer.Block1561.cells ++
  DirichletL.ContourCertificates.Outer.Block1562.cells ++
  DirichletL.ContourCertificates.Outer.Block1563.cells ++
  DirichletL.ContourCertificates.Outer.Block1564.cells ++
  DirichletL.ContourCertificates.Outer.Block1565.cells ++
  DirichletL.ContourCertificates.Outer.Block1566.cells ++
  DirichletL.ContourCertificates.Outer.Block1567.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1560.cells_bounded, DirichletL.ContourCertificates.Outer.Block1561.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1562.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1563.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1564.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1565.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1566.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1567.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch195
