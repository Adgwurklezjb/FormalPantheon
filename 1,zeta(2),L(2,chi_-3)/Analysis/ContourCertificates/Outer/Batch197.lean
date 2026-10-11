import Analysis.ContourCertificates.Outer.Block1576
import Analysis.ContourCertificates.Outer.Block1577
import Analysis.ContourCertificates.Outer.Block1578
import Analysis.ContourCertificates.Outer.Block1579
import Analysis.ContourCertificates.Outer.Block1580
import Analysis.ContourCertificates.Outer.Block1581
import Analysis.ContourCertificates.Outer.Block1582
import Analysis.ContourCertificates.Outer.Block1583

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch197

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1576.cells ++
  DirichletL.ContourCertificates.Outer.Block1577.cells ++
  DirichletL.ContourCertificates.Outer.Block1578.cells ++
  DirichletL.ContourCertificates.Outer.Block1579.cells ++
  DirichletL.ContourCertificates.Outer.Block1580.cells ++
  DirichletL.ContourCertificates.Outer.Block1581.cells ++
  DirichletL.ContourCertificates.Outer.Block1582.cells ++
  DirichletL.ContourCertificates.Outer.Block1583.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1576.cells_bounded, DirichletL.ContourCertificates.Outer.Block1577.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1578.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1579.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1580.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1581.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1582.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1583.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch197
