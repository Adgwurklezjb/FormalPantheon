import Analysis.ContourCertificates.Outer.Block1344
import Analysis.ContourCertificates.Outer.Block1345
import Analysis.ContourCertificates.Outer.Block1346
import Analysis.ContourCertificates.Outer.Block1347
import Analysis.ContourCertificates.Outer.Block1348
import Analysis.ContourCertificates.Outer.Block1349
import Analysis.ContourCertificates.Outer.Block1350
import Analysis.ContourCertificates.Outer.Block1351

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch168

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1344.cells ++
  DirichletL.ContourCertificates.Outer.Block1345.cells ++
  DirichletL.ContourCertificates.Outer.Block1346.cells ++
  DirichletL.ContourCertificates.Outer.Block1347.cells ++
  DirichletL.ContourCertificates.Outer.Block1348.cells ++
  DirichletL.ContourCertificates.Outer.Block1349.cells ++
  DirichletL.ContourCertificates.Outer.Block1350.cells ++
  DirichletL.ContourCertificates.Outer.Block1351.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1344.cells_bounded, DirichletL.ContourCertificates.Outer.Block1345.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1346.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1347.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1348.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1349.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1350.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1351.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch168
