import Analysis.ContourCertificates.Outer.Block1208
import Analysis.ContourCertificates.Outer.Block1209
import Analysis.ContourCertificates.Outer.Block1210
import Analysis.ContourCertificates.Outer.Block1211
import Analysis.ContourCertificates.Outer.Block1212
import Analysis.ContourCertificates.Outer.Block1213
import Analysis.ContourCertificates.Outer.Block1214
import Analysis.ContourCertificates.Outer.Block1215

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch151

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1208.cells ++
  DirichletL.ContourCertificates.Outer.Block1209.cells ++
  DirichletL.ContourCertificates.Outer.Block1210.cells ++
  DirichletL.ContourCertificates.Outer.Block1211.cells ++
  DirichletL.ContourCertificates.Outer.Block1212.cells ++
  DirichletL.ContourCertificates.Outer.Block1213.cells ++
  DirichletL.ContourCertificates.Outer.Block1214.cells ++
  DirichletL.ContourCertificates.Outer.Block1215.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1208.cells_bounded, DirichletL.ContourCertificates.Outer.Block1209.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1210.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1211.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1212.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1213.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1214.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1215.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch151
