import Analysis.ContourCertificates.Outer.Block1568
import Analysis.ContourCertificates.Outer.Block1569
import Analysis.ContourCertificates.Outer.Block1570
import Analysis.ContourCertificates.Outer.Block1571
import Analysis.ContourCertificates.Outer.Block1572
import Analysis.ContourCertificates.Outer.Block1573
import Analysis.ContourCertificates.Outer.Block1574
import Analysis.ContourCertificates.Outer.Block1575

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch196

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1568.cells ++
  DirichletL.ContourCertificates.Outer.Block1569.cells ++
  DirichletL.ContourCertificates.Outer.Block1570.cells ++
  DirichletL.ContourCertificates.Outer.Block1571.cells ++
  DirichletL.ContourCertificates.Outer.Block1572.cells ++
  DirichletL.ContourCertificates.Outer.Block1573.cells ++
  DirichletL.ContourCertificates.Outer.Block1574.cells ++
  DirichletL.ContourCertificates.Outer.Block1575.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1568.cells_bounded, DirichletL.ContourCertificates.Outer.Block1569.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1570.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1571.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1572.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1573.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1574.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1575.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch196
