import Analysis.ContourCertificates.Outer.Block1152
import Analysis.ContourCertificates.Outer.Block1153
import Analysis.ContourCertificates.Outer.Block1154
import Analysis.ContourCertificates.Outer.Block1155
import Analysis.ContourCertificates.Outer.Block1156
import Analysis.ContourCertificates.Outer.Block1157
import Analysis.ContourCertificates.Outer.Block1158
import Analysis.ContourCertificates.Outer.Block1159

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch144

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1152.cells ++
  DirichletL.ContourCertificates.Outer.Block1153.cells ++
  DirichletL.ContourCertificates.Outer.Block1154.cells ++
  DirichletL.ContourCertificates.Outer.Block1155.cells ++
  DirichletL.ContourCertificates.Outer.Block1156.cells ++
  DirichletL.ContourCertificates.Outer.Block1157.cells ++
  DirichletL.ContourCertificates.Outer.Block1158.cells ++
  DirichletL.ContourCertificates.Outer.Block1159.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1152.cells_bounded, DirichletL.ContourCertificates.Outer.Block1153.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1154.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1155.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1156.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1157.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1158.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1159.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch144
