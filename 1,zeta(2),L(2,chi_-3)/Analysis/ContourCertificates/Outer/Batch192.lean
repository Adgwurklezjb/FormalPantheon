import Analysis.ContourCertificates.Outer.Block1536
import Analysis.ContourCertificates.Outer.Block1537
import Analysis.ContourCertificates.Outer.Block1538
import Analysis.ContourCertificates.Outer.Block1539
import Analysis.ContourCertificates.Outer.Block1540
import Analysis.ContourCertificates.Outer.Block1541
import Analysis.ContourCertificates.Outer.Block1542
import Analysis.ContourCertificates.Outer.Block1543

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch192

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1536.cells ++
  DirichletL.ContourCertificates.Outer.Block1537.cells ++
  DirichletL.ContourCertificates.Outer.Block1538.cells ++
  DirichletL.ContourCertificates.Outer.Block1539.cells ++
  DirichletL.ContourCertificates.Outer.Block1540.cells ++
  DirichletL.ContourCertificates.Outer.Block1541.cells ++
  DirichletL.ContourCertificates.Outer.Block1542.cells ++
  DirichletL.ContourCertificates.Outer.Block1543.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1536.cells_bounded, DirichletL.ContourCertificates.Outer.Block1537.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1538.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1539.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1540.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1541.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1542.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1543.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch192
