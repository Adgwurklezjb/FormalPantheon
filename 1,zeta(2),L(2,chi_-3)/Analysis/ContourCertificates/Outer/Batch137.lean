import Analysis.ContourCertificates.Outer.Block1096
import Analysis.ContourCertificates.Outer.Block1097
import Analysis.ContourCertificates.Outer.Block1098
import Analysis.ContourCertificates.Outer.Block1099
import Analysis.ContourCertificates.Outer.Block1100
import Analysis.ContourCertificates.Outer.Block1101
import Analysis.ContourCertificates.Outer.Block1102
import Analysis.ContourCertificates.Outer.Block1103

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch137

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1096.cells ++
  DirichletL.ContourCertificates.Outer.Block1097.cells ++
  DirichletL.ContourCertificates.Outer.Block1098.cells ++
  DirichletL.ContourCertificates.Outer.Block1099.cells ++
  DirichletL.ContourCertificates.Outer.Block1100.cells ++
  DirichletL.ContourCertificates.Outer.Block1101.cells ++
  DirichletL.ContourCertificates.Outer.Block1102.cells ++
  DirichletL.ContourCertificates.Outer.Block1103.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1096.cells_bounded, DirichletL.ContourCertificates.Outer.Block1097.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1098.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1099.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1100.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1101.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1102.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1103.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch137
