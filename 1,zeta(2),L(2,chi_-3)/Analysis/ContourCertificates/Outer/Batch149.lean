import Analysis.ContourCertificates.Outer.Block1192
import Analysis.ContourCertificates.Outer.Block1193
import Analysis.ContourCertificates.Outer.Block1194
import Analysis.ContourCertificates.Outer.Block1195
import Analysis.ContourCertificates.Outer.Block1196
import Analysis.ContourCertificates.Outer.Block1197
import Analysis.ContourCertificates.Outer.Block1198
import Analysis.ContourCertificates.Outer.Block1199

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch149

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1192.cells ++
  DirichletL.ContourCertificates.Outer.Block1193.cells ++
  DirichletL.ContourCertificates.Outer.Block1194.cells ++
  DirichletL.ContourCertificates.Outer.Block1195.cells ++
  DirichletL.ContourCertificates.Outer.Block1196.cells ++
  DirichletL.ContourCertificates.Outer.Block1197.cells ++
  DirichletL.ContourCertificates.Outer.Block1198.cells ++
  DirichletL.ContourCertificates.Outer.Block1199.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1192.cells_bounded, DirichletL.ContourCertificates.Outer.Block1193.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1194.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1195.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1196.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1197.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1198.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1199.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch149
