import Analysis.ContourCertificates.Outer.Block1368
import Analysis.ContourCertificates.Outer.Block1369
import Analysis.ContourCertificates.Outer.Block1370
import Analysis.ContourCertificates.Outer.Block1371
import Analysis.ContourCertificates.Outer.Block1372
import Analysis.ContourCertificates.Outer.Block1373
import Analysis.ContourCertificates.Outer.Block1374
import Analysis.ContourCertificates.Outer.Block1375

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch171

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1368.cells ++
  DirichletL.ContourCertificates.Outer.Block1369.cells ++
  DirichletL.ContourCertificates.Outer.Block1370.cells ++
  DirichletL.ContourCertificates.Outer.Block1371.cells ++
  DirichletL.ContourCertificates.Outer.Block1372.cells ++
  DirichletL.ContourCertificates.Outer.Block1373.cells ++
  DirichletL.ContourCertificates.Outer.Block1374.cells ++
  DirichletL.ContourCertificates.Outer.Block1375.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1368.cells_bounded, DirichletL.ContourCertificates.Outer.Block1369.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1370.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1371.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1372.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1373.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1374.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1375.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch171
