import Analysis.ContourCertificates.Outer.Block1240
import Analysis.ContourCertificates.Outer.Block1241
import Analysis.ContourCertificates.Outer.Block1242
import Analysis.ContourCertificates.Outer.Block1243
import Analysis.ContourCertificates.Outer.Block1244
import Analysis.ContourCertificates.Outer.Block1245
import Analysis.ContourCertificates.Outer.Block1246
import Analysis.ContourCertificates.Outer.Block1247

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch155

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1240.cells ++
  DirichletL.ContourCertificates.Outer.Block1241.cells ++
  DirichletL.ContourCertificates.Outer.Block1242.cells ++
  DirichletL.ContourCertificates.Outer.Block1243.cells ++
  DirichletL.ContourCertificates.Outer.Block1244.cells ++
  DirichletL.ContourCertificates.Outer.Block1245.cells ++
  DirichletL.ContourCertificates.Outer.Block1246.cells ++
  DirichletL.ContourCertificates.Outer.Block1247.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1240.cells_bounded, DirichletL.ContourCertificates.Outer.Block1241.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1242.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1243.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1244.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1245.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1246.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1247.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch155
