import Analysis.ContourCertificates.Outer.Block1528
import Analysis.ContourCertificates.Outer.Block1529
import Analysis.ContourCertificates.Outer.Block1530
import Analysis.ContourCertificates.Outer.Block1531
import Analysis.ContourCertificates.Outer.Block1532
import Analysis.ContourCertificates.Outer.Block1533
import Analysis.ContourCertificates.Outer.Block1534
import Analysis.ContourCertificates.Outer.Block1535

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch191

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1528.cells ++
  DirichletL.ContourCertificates.Outer.Block1529.cells ++
  DirichletL.ContourCertificates.Outer.Block1530.cells ++
  DirichletL.ContourCertificates.Outer.Block1531.cells ++
  DirichletL.ContourCertificates.Outer.Block1532.cells ++
  DirichletL.ContourCertificates.Outer.Block1533.cells ++
  DirichletL.ContourCertificates.Outer.Block1534.cells ++
  DirichletL.ContourCertificates.Outer.Block1535.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1528.cells_bounded, DirichletL.ContourCertificates.Outer.Block1529.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1530.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1531.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1532.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1533.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1534.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1535.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch191
