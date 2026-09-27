import Analysis.ContourCertificates.Outer.Block1400
import Analysis.ContourCertificates.Outer.Block1401
import Analysis.ContourCertificates.Outer.Block1402
import Analysis.ContourCertificates.Outer.Block1403
import Analysis.ContourCertificates.Outer.Block1404
import Analysis.ContourCertificates.Outer.Block1405
import Analysis.ContourCertificates.Outer.Block1406
import Analysis.ContourCertificates.Outer.Block1407

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch175

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1400.cells ++
  DirichletL.ContourCertificates.Outer.Block1401.cells ++
  DirichletL.ContourCertificates.Outer.Block1402.cells ++
  DirichletL.ContourCertificates.Outer.Block1403.cells ++
  DirichletL.ContourCertificates.Outer.Block1404.cells ++
  DirichletL.ContourCertificates.Outer.Block1405.cells ++
  DirichletL.ContourCertificates.Outer.Block1406.cells ++
  DirichletL.ContourCertificates.Outer.Block1407.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1400.cells_bounded, DirichletL.ContourCertificates.Outer.Block1401.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1402.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1403.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1404.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1405.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1406.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1407.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch175
