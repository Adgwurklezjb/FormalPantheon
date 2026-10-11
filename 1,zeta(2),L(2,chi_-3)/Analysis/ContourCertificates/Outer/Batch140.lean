import Analysis.ContourCertificates.Outer.Block1120
import Analysis.ContourCertificates.Outer.Block1121
import Analysis.ContourCertificates.Outer.Block1122
import Analysis.ContourCertificates.Outer.Block1123
import Analysis.ContourCertificates.Outer.Block1124
import Analysis.ContourCertificates.Outer.Block1125
import Analysis.ContourCertificates.Outer.Block1126
import Analysis.ContourCertificates.Outer.Block1127

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch140

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1120.cells ++
  DirichletL.ContourCertificates.Outer.Block1121.cells ++
  DirichletL.ContourCertificates.Outer.Block1122.cells ++
  DirichletL.ContourCertificates.Outer.Block1123.cells ++
  DirichletL.ContourCertificates.Outer.Block1124.cells ++
  DirichletL.ContourCertificates.Outer.Block1125.cells ++
  DirichletL.ContourCertificates.Outer.Block1126.cells ++
  DirichletL.ContourCertificates.Outer.Block1127.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1120.cells_bounded, DirichletL.ContourCertificates.Outer.Block1121.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1122.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1123.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1124.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1125.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1126.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1127.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch140
