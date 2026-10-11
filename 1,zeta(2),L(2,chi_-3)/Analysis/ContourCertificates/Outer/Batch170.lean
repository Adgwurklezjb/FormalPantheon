import Analysis.ContourCertificates.Outer.Block1360
import Analysis.ContourCertificates.Outer.Block1361
import Analysis.ContourCertificates.Outer.Block1362
import Analysis.ContourCertificates.Outer.Block1363
import Analysis.ContourCertificates.Outer.Block1364
import Analysis.ContourCertificates.Outer.Block1365
import Analysis.ContourCertificates.Outer.Block1366
import Analysis.ContourCertificates.Outer.Block1367

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch170

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1360.cells ++
  DirichletL.ContourCertificates.Outer.Block1361.cells ++
  DirichletL.ContourCertificates.Outer.Block1362.cells ++
  DirichletL.ContourCertificates.Outer.Block1363.cells ++
  DirichletL.ContourCertificates.Outer.Block1364.cells ++
  DirichletL.ContourCertificates.Outer.Block1365.cells ++
  DirichletL.ContourCertificates.Outer.Block1366.cells ++
  DirichletL.ContourCertificates.Outer.Block1367.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1360.cells_bounded, DirichletL.ContourCertificates.Outer.Block1361.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1362.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1363.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1364.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1365.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1366.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1367.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch170
