import Analysis.ContourCertificates.Outer.Block1136
import Analysis.ContourCertificates.Outer.Block1137
import Analysis.ContourCertificates.Outer.Block1138
import Analysis.ContourCertificates.Outer.Block1139
import Analysis.ContourCertificates.Outer.Block1140
import Analysis.ContourCertificates.Outer.Block1141
import Analysis.ContourCertificates.Outer.Block1142
import Analysis.ContourCertificates.Outer.Block1143

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch142

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1136.cells ++
  DirichletL.ContourCertificates.Outer.Block1137.cells ++
  DirichletL.ContourCertificates.Outer.Block1138.cells ++
  DirichletL.ContourCertificates.Outer.Block1139.cells ++
  DirichletL.ContourCertificates.Outer.Block1140.cells ++
  DirichletL.ContourCertificates.Outer.Block1141.cells ++
  DirichletL.ContourCertificates.Outer.Block1142.cells ++
  DirichletL.ContourCertificates.Outer.Block1143.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1136.cells_bounded, DirichletL.ContourCertificates.Outer.Block1137.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1138.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1139.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1140.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1141.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1142.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1143.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch142
