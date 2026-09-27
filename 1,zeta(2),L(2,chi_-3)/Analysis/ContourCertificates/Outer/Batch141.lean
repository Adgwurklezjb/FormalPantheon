import Analysis.ContourCertificates.Outer.Block1128
import Analysis.ContourCertificates.Outer.Block1129
import Analysis.ContourCertificates.Outer.Block1130
import Analysis.ContourCertificates.Outer.Block1131
import Analysis.ContourCertificates.Outer.Block1132
import Analysis.ContourCertificates.Outer.Block1133
import Analysis.ContourCertificates.Outer.Block1134
import Analysis.ContourCertificates.Outer.Block1135

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch141

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1128.cells ++
  DirichletL.ContourCertificates.Outer.Block1129.cells ++
  DirichletL.ContourCertificates.Outer.Block1130.cells ++
  DirichletL.ContourCertificates.Outer.Block1131.cells ++
  DirichletL.ContourCertificates.Outer.Block1132.cells ++
  DirichletL.ContourCertificates.Outer.Block1133.cells ++
  DirichletL.ContourCertificates.Outer.Block1134.cells ++
  DirichletL.ContourCertificates.Outer.Block1135.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1128.cells_bounded, DirichletL.ContourCertificates.Outer.Block1129.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1130.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1131.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1132.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1133.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1134.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1135.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch141
