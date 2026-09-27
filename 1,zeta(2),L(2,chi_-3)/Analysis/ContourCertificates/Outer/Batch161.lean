import Analysis.ContourCertificates.Outer.Block1288
import Analysis.ContourCertificates.Outer.Block1289
import Analysis.ContourCertificates.Outer.Block1290
import Analysis.ContourCertificates.Outer.Block1291
import Analysis.ContourCertificates.Outer.Block1292
import Analysis.ContourCertificates.Outer.Block1293
import Analysis.ContourCertificates.Outer.Block1294
import Analysis.ContourCertificates.Outer.Block1295

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch161

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1288.cells ++
  DirichletL.ContourCertificates.Outer.Block1289.cells ++
  DirichletL.ContourCertificates.Outer.Block1290.cells ++
  DirichletL.ContourCertificates.Outer.Block1291.cells ++
  DirichletL.ContourCertificates.Outer.Block1292.cells ++
  DirichletL.ContourCertificates.Outer.Block1293.cells ++
  DirichletL.ContourCertificates.Outer.Block1294.cells ++
  DirichletL.ContourCertificates.Outer.Block1295.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1288.cells_bounded, DirichletL.ContourCertificates.Outer.Block1289.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1290.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1291.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1292.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1293.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1294.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1295.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch161
