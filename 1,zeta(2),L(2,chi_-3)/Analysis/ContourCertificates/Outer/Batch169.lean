import Analysis.ContourCertificates.Outer.Block1352
import Analysis.ContourCertificates.Outer.Block1353
import Analysis.ContourCertificates.Outer.Block1354
import Analysis.ContourCertificates.Outer.Block1355
import Analysis.ContourCertificates.Outer.Block1356
import Analysis.ContourCertificates.Outer.Block1357
import Analysis.ContourCertificates.Outer.Block1358
import Analysis.ContourCertificates.Outer.Block1359

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch169

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1352.cells ++
  DirichletL.ContourCertificates.Outer.Block1353.cells ++
  DirichletL.ContourCertificates.Outer.Block1354.cells ++
  DirichletL.ContourCertificates.Outer.Block1355.cells ++
  DirichletL.ContourCertificates.Outer.Block1356.cells ++
  DirichletL.ContourCertificates.Outer.Block1357.cells ++
  DirichletL.ContourCertificates.Outer.Block1358.cells ++
  DirichletL.ContourCertificates.Outer.Block1359.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1352.cells_bounded, DirichletL.ContourCertificates.Outer.Block1353.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1354.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1355.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1356.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1357.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1358.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1359.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch169
