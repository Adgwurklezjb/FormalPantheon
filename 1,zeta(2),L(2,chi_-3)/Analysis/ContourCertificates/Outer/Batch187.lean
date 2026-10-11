import Analysis.ContourCertificates.Outer.Block1496
import Analysis.ContourCertificates.Outer.Block1497
import Analysis.ContourCertificates.Outer.Block1498
import Analysis.ContourCertificates.Outer.Block1499
import Analysis.ContourCertificates.Outer.Block1500
import Analysis.ContourCertificates.Outer.Block1501
import Analysis.ContourCertificates.Outer.Block1502
import Analysis.ContourCertificates.Outer.Block1503

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch187

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1496.cells ++
  DirichletL.ContourCertificates.Outer.Block1497.cells ++
  DirichletL.ContourCertificates.Outer.Block1498.cells ++
  DirichletL.ContourCertificates.Outer.Block1499.cells ++
  DirichletL.ContourCertificates.Outer.Block1500.cells ++
  DirichletL.ContourCertificates.Outer.Block1501.cells ++
  DirichletL.ContourCertificates.Outer.Block1502.cells ++
  DirichletL.ContourCertificates.Outer.Block1503.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1496.cells_bounded, DirichletL.ContourCertificates.Outer.Block1497.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1498.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1499.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1500.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1501.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1502.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1503.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch187
