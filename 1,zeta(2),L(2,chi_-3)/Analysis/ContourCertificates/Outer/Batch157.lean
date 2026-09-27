import Analysis.ContourCertificates.Outer.Block1256
import Analysis.ContourCertificates.Outer.Block1257
import Analysis.ContourCertificates.Outer.Block1258
import Analysis.ContourCertificates.Outer.Block1259
import Analysis.ContourCertificates.Outer.Block1260
import Analysis.ContourCertificates.Outer.Block1261
import Analysis.ContourCertificates.Outer.Block1262
import Analysis.ContourCertificates.Outer.Block1263

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch157

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1256.cells ++
  DirichletL.ContourCertificates.Outer.Block1257.cells ++
  DirichletL.ContourCertificates.Outer.Block1258.cells ++
  DirichletL.ContourCertificates.Outer.Block1259.cells ++
  DirichletL.ContourCertificates.Outer.Block1260.cells ++
  DirichletL.ContourCertificates.Outer.Block1261.cells ++
  DirichletL.ContourCertificates.Outer.Block1262.cells ++
  DirichletL.ContourCertificates.Outer.Block1263.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1256.cells_bounded, DirichletL.ContourCertificates.Outer.Block1257.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1258.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1259.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1260.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1261.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1262.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1263.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch157
