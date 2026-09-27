import Analysis.ContourCertificates.Outer.Block1512
import Analysis.ContourCertificates.Outer.Block1513
import Analysis.ContourCertificates.Outer.Block1514
import Analysis.ContourCertificates.Outer.Block1515
import Analysis.ContourCertificates.Outer.Block1516
import Analysis.ContourCertificates.Outer.Block1517
import Analysis.ContourCertificates.Outer.Block1518
import Analysis.ContourCertificates.Outer.Block1519

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch189

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1512.cells ++
  DirichletL.ContourCertificates.Outer.Block1513.cells ++
  DirichletL.ContourCertificates.Outer.Block1514.cells ++
  DirichletL.ContourCertificates.Outer.Block1515.cells ++
  DirichletL.ContourCertificates.Outer.Block1516.cells ++
  DirichletL.ContourCertificates.Outer.Block1517.cells ++
  DirichletL.ContourCertificates.Outer.Block1518.cells ++
  DirichletL.ContourCertificates.Outer.Block1519.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1512.cells_bounded, DirichletL.ContourCertificates.Outer.Block1513.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1514.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1515.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1516.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1517.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1518.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1519.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch189
