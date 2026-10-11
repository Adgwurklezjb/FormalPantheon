import Analysis.ContourCertificates.Outer.Block1104
import Analysis.ContourCertificates.Outer.Block1105
import Analysis.ContourCertificates.Outer.Block1106
import Analysis.ContourCertificates.Outer.Block1107
import Analysis.ContourCertificates.Outer.Block1108
import Analysis.ContourCertificates.Outer.Block1109
import Analysis.ContourCertificates.Outer.Block1110
import Analysis.ContourCertificates.Outer.Block1111

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch138

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1104.cells ++
  DirichletL.ContourCertificates.Outer.Block1105.cells ++
  DirichletL.ContourCertificates.Outer.Block1106.cells ++
  DirichletL.ContourCertificates.Outer.Block1107.cells ++
  DirichletL.ContourCertificates.Outer.Block1108.cells ++
  DirichletL.ContourCertificates.Outer.Block1109.cells ++
  DirichletL.ContourCertificates.Outer.Block1110.cells ++
  DirichletL.ContourCertificates.Outer.Block1111.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1104.cells_bounded, DirichletL.ContourCertificates.Outer.Block1105.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1106.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1107.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1108.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1109.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1110.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1111.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch138
