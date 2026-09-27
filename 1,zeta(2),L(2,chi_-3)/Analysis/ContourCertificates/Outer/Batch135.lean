import Analysis.ContourCertificates.Outer.Block1080
import Analysis.ContourCertificates.Outer.Block1081
import Analysis.ContourCertificates.Outer.Block1082
import Analysis.ContourCertificates.Outer.Block1083
import Analysis.ContourCertificates.Outer.Block1084
import Analysis.ContourCertificates.Outer.Block1085
import Analysis.ContourCertificates.Outer.Block1086
import Analysis.ContourCertificates.Outer.Block1087

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch135

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1080.cells ++
  DirichletL.ContourCertificates.Outer.Block1081.cells ++
  DirichletL.ContourCertificates.Outer.Block1082.cells ++
  DirichletL.ContourCertificates.Outer.Block1083.cells ++
  DirichletL.ContourCertificates.Outer.Block1084.cells ++
  DirichletL.ContourCertificates.Outer.Block1085.cells ++
  DirichletL.ContourCertificates.Outer.Block1086.cells ++
  DirichletL.ContourCertificates.Outer.Block1087.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1080.cells_bounded, DirichletL.ContourCertificates.Outer.Block1081.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1082.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1083.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1084.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1085.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1086.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1087.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch135
