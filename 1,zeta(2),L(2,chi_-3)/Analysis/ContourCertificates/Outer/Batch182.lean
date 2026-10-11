import Analysis.ContourCertificates.Outer.Block1456
import Analysis.ContourCertificates.Outer.Block1457
import Analysis.ContourCertificates.Outer.Block1458
import Analysis.ContourCertificates.Outer.Block1459
import Analysis.ContourCertificates.Outer.Block1460
import Analysis.ContourCertificates.Outer.Block1461
import Analysis.ContourCertificates.Outer.Block1462
import Analysis.ContourCertificates.Outer.Block1463

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch182

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1456.cells ++
  DirichletL.ContourCertificates.Outer.Block1457.cells ++
  DirichletL.ContourCertificates.Outer.Block1458.cells ++
  DirichletL.ContourCertificates.Outer.Block1459.cells ++
  DirichletL.ContourCertificates.Outer.Block1460.cells ++
  DirichletL.ContourCertificates.Outer.Block1461.cells ++
  DirichletL.ContourCertificates.Outer.Block1462.cells ++
  DirichletL.ContourCertificates.Outer.Block1463.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1456.cells_bounded, DirichletL.ContourCertificates.Outer.Block1457.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1458.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1459.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1460.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1461.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1462.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1463.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch182
