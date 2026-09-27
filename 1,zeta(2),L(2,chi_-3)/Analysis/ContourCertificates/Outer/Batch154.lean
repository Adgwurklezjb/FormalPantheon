import Analysis.ContourCertificates.Outer.Block1232
import Analysis.ContourCertificates.Outer.Block1233
import Analysis.ContourCertificates.Outer.Block1234
import Analysis.ContourCertificates.Outer.Block1235
import Analysis.ContourCertificates.Outer.Block1236
import Analysis.ContourCertificates.Outer.Block1237
import Analysis.ContourCertificates.Outer.Block1238
import Analysis.ContourCertificates.Outer.Block1239

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch154

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1232.cells ++
  DirichletL.ContourCertificates.Outer.Block1233.cells ++
  DirichletL.ContourCertificates.Outer.Block1234.cells ++
  DirichletL.ContourCertificates.Outer.Block1235.cells ++
  DirichletL.ContourCertificates.Outer.Block1236.cells ++
  DirichletL.ContourCertificates.Outer.Block1237.cells ++
  DirichletL.ContourCertificates.Outer.Block1238.cells ++
  DirichletL.ContourCertificates.Outer.Block1239.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1232.cells_bounded, DirichletL.ContourCertificates.Outer.Block1233.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1234.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1235.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1236.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1237.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1238.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1239.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch154
