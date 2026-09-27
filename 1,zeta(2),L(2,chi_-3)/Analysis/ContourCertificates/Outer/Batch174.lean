import Analysis.ContourCertificates.Outer.Block1392
import Analysis.ContourCertificates.Outer.Block1393
import Analysis.ContourCertificates.Outer.Block1394
import Analysis.ContourCertificates.Outer.Block1395
import Analysis.ContourCertificates.Outer.Block1396
import Analysis.ContourCertificates.Outer.Block1397
import Analysis.ContourCertificates.Outer.Block1398
import Analysis.ContourCertificates.Outer.Block1399

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch174

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1392.cells ++
  DirichletL.ContourCertificates.Outer.Block1393.cells ++
  DirichletL.ContourCertificates.Outer.Block1394.cells ++
  DirichletL.ContourCertificates.Outer.Block1395.cells ++
  DirichletL.ContourCertificates.Outer.Block1396.cells ++
  DirichletL.ContourCertificates.Outer.Block1397.cells ++
  DirichletL.ContourCertificates.Outer.Block1398.cells ++
  DirichletL.ContourCertificates.Outer.Block1399.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1392.cells_bounded, DirichletL.ContourCertificates.Outer.Block1393.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1394.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1395.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1396.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1397.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1398.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1399.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch174
