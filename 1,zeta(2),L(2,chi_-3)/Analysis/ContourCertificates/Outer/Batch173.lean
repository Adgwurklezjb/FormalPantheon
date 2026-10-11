import Analysis.ContourCertificates.Outer.Block1384
import Analysis.ContourCertificates.Outer.Block1385
import Analysis.ContourCertificates.Outer.Block1386
import Analysis.ContourCertificates.Outer.Block1387
import Analysis.ContourCertificates.Outer.Block1388
import Analysis.ContourCertificates.Outer.Block1389
import Analysis.ContourCertificates.Outer.Block1390
import Analysis.ContourCertificates.Outer.Block1391

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch173

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1384.cells ++
  DirichletL.ContourCertificates.Outer.Block1385.cells ++
  DirichletL.ContourCertificates.Outer.Block1386.cells ++
  DirichletL.ContourCertificates.Outer.Block1387.cells ++
  DirichletL.ContourCertificates.Outer.Block1388.cells ++
  DirichletL.ContourCertificates.Outer.Block1389.cells ++
  DirichletL.ContourCertificates.Outer.Block1390.cells ++
  DirichletL.ContourCertificates.Outer.Block1391.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1384.cells_bounded, DirichletL.ContourCertificates.Outer.Block1385.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1386.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1387.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1388.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1389.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1390.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1391.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch173
