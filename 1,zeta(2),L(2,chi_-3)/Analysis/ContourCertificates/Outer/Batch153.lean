import Analysis.ContourCertificates.Outer.Block1224
import Analysis.ContourCertificates.Outer.Block1225
import Analysis.ContourCertificates.Outer.Block1226
import Analysis.ContourCertificates.Outer.Block1227
import Analysis.ContourCertificates.Outer.Block1228
import Analysis.ContourCertificates.Outer.Block1229
import Analysis.ContourCertificates.Outer.Block1230
import Analysis.ContourCertificates.Outer.Block1231

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch153

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1224.cells ++
  DirichletL.ContourCertificates.Outer.Block1225.cells ++
  DirichletL.ContourCertificates.Outer.Block1226.cells ++
  DirichletL.ContourCertificates.Outer.Block1227.cells ++
  DirichletL.ContourCertificates.Outer.Block1228.cells ++
  DirichletL.ContourCertificates.Outer.Block1229.cells ++
  DirichletL.ContourCertificates.Outer.Block1230.cells ++
  DirichletL.ContourCertificates.Outer.Block1231.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1224.cells_bounded, DirichletL.ContourCertificates.Outer.Block1225.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1226.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1227.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1228.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1229.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1230.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1231.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch153
