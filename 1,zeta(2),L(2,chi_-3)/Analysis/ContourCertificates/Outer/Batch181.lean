import Analysis.ContourCertificates.Outer.Block1448
import Analysis.ContourCertificates.Outer.Block1449
import Analysis.ContourCertificates.Outer.Block1450
import Analysis.ContourCertificates.Outer.Block1451
import Analysis.ContourCertificates.Outer.Block1452
import Analysis.ContourCertificates.Outer.Block1453
import Analysis.ContourCertificates.Outer.Block1454
import Analysis.ContourCertificates.Outer.Block1455

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch181

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1448.cells ++
  DirichletL.ContourCertificates.Outer.Block1449.cells ++
  DirichletL.ContourCertificates.Outer.Block1450.cells ++
  DirichletL.ContourCertificates.Outer.Block1451.cells ++
  DirichletL.ContourCertificates.Outer.Block1452.cells ++
  DirichletL.ContourCertificates.Outer.Block1453.cells ++
  DirichletL.ContourCertificates.Outer.Block1454.cells ++
  DirichletL.ContourCertificates.Outer.Block1455.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1448.cells_bounded, DirichletL.ContourCertificates.Outer.Block1449.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1450.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1451.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1452.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1453.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1454.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1455.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch181
