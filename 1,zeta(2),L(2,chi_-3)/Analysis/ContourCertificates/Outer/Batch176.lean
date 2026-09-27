import Analysis.ContourCertificates.Outer.Block1408
import Analysis.ContourCertificates.Outer.Block1409
import Analysis.ContourCertificates.Outer.Block1410
import Analysis.ContourCertificates.Outer.Block1411
import Analysis.ContourCertificates.Outer.Block1412
import Analysis.ContourCertificates.Outer.Block1413
import Analysis.ContourCertificates.Outer.Block1414
import Analysis.ContourCertificates.Outer.Block1415

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch176

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1408.cells ++
  DirichletL.ContourCertificates.Outer.Block1409.cells ++
  DirichletL.ContourCertificates.Outer.Block1410.cells ++
  DirichletL.ContourCertificates.Outer.Block1411.cells ++
  DirichletL.ContourCertificates.Outer.Block1412.cells ++
  DirichletL.ContourCertificates.Outer.Block1413.cells ++
  DirichletL.ContourCertificates.Outer.Block1414.cells ++
  DirichletL.ContourCertificates.Outer.Block1415.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1408.cells_bounded, DirichletL.ContourCertificates.Outer.Block1409.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1410.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1411.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1412.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1413.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1414.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1415.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch176
