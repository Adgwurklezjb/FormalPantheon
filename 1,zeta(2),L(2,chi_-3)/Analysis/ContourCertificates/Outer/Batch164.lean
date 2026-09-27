import Analysis.ContourCertificates.Outer.Block1312
import Analysis.ContourCertificates.Outer.Block1313
import Analysis.ContourCertificates.Outer.Block1314
import Analysis.ContourCertificates.Outer.Block1315
import Analysis.ContourCertificates.Outer.Block1316
import Analysis.ContourCertificates.Outer.Block1317
import Analysis.ContourCertificates.Outer.Block1318
import Analysis.ContourCertificates.Outer.Block1319

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch164

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1312.cells ++
  DirichletL.ContourCertificates.Outer.Block1313.cells ++
  DirichletL.ContourCertificates.Outer.Block1314.cells ++
  DirichletL.ContourCertificates.Outer.Block1315.cells ++
  DirichletL.ContourCertificates.Outer.Block1316.cells ++
  DirichletL.ContourCertificates.Outer.Block1317.cells ++
  DirichletL.ContourCertificates.Outer.Block1318.cells ++
  DirichletL.ContourCertificates.Outer.Block1319.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1312.cells_bounded, DirichletL.ContourCertificates.Outer.Block1313.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1314.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1315.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1316.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1317.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1318.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1319.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch164
