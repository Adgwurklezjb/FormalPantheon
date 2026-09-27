import Analysis.ContourCertificates.Outer.Block1472
import Analysis.ContourCertificates.Outer.Block1473
import Analysis.ContourCertificates.Outer.Block1474
import Analysis.ContourCertificates.Outer.Block1475
import Analysis.ContourCertificates.Outer.Block1476
import Analysis.ContourCertificates.Outer.Block1477
import Analysis.ContourCertificates.Outer.Block1478
import Analysis.ContourCertificates.Outer.Block1479

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch184

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1472.cells ++
  DirichletL.ContourCertificates.Outer.Block1473.cells ++
  DirichletL.ContourCertificates.Outer.Block1474.cells ++
  DirichletL.ContourCertificates.Outer.Block1475.cells ++
  DirichletL.ContourCertificates.Outer.Block1476.cells ++
  DirichletL.ContourCertificates.Outer.Block1477.cells ++
  DirichletL.ContourCertificates.Outer.Block1478.cells ++
  DirichletL.ContourCertificates.Outer.Block1479.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1472.cells_bounded, DirichletL.ContourCertificates.Outer.Block1473.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1474.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1475.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1476.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1477.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1478.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1479.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch184
