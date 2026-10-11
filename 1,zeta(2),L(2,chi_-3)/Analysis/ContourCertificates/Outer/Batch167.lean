import Analysis.ContourCertificates.Outer.Block1336
import Analysis.ContourCertificates.Outer.Block1337
import Analysis.ContourCertificates.Outer.Block1338
import Analysis.ContourCertificates.Outer.Block1339
import Analysis.ContourCertificates.Outer.Block1340
import Analysis.ContourCertificates.Outer.Block1341
import Analysis.ContourCertificates.Outer.Block1342
import Analysis.ContourCertificates.Outer.Block1343

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch167

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1336.cells ++
  DirichletL.ContourCertificates.Outer.Block1337.cells ++
  DirichletL.ContourCertificates.Outer.Block1338.cells ++
  DirichletL.ContourCertificates.Outer.Block1339.cells ++
  DirichletL.ContourCertificates.Outer.Block1340.cells ++
  DirichletL.ContourCertificates.Outer.Block1341.cells ++
  DirichletL.ContourCertificates.Outer.Block1342.cells ++
  DirichletL.ContourCertificates.Outer.Block1343.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1336.cells_bounded, DirichletL.ContourCertificates.Outer.Block1337.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1338.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1339.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1340.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1341.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1342.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1343.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch167
