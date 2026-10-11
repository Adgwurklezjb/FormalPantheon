import Analysis.ContourCertificates.Outer.Block1504
import Analysis.ContourCertificates.Outer.Block1505
import Analysis.ContourCertificates.Outer.Block1506
import Analysis.ContourCertificates.Outer.Block1507
import Analysis.ContourCertificates.Outer.Block1508
import Analysis.ContourCertificates.Outer.Block1509
import Analysis.ContourCertificates.Outer.Block1510
import Analysis.ContourCertificates.Outer.Block1511

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch188

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1504.cells ++
  DirichletL.ContourCertificates.Outer.Block1505.cells ++
  DirichletL.ContourCertificates.Outer.Block1506.cells ++
  DirichletL.ContourCertificates.Outer.Block1507.cells ++
  DirichletL.ContourCertificates.Outer.Block1508.cells ++
  DirichletL.ContourCertificates.Outer.Block1509.cells ++
  DirichletL.ContourCertificates.Outer.Block1510.cells ++
  DirichletL.ContourCertificates.Outer.Block1511.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1504.cells_bounded, DirichletL.ContourCertificates.Outer.Block1505.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1506.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1507.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1508.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1509.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1510.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1511.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch188
