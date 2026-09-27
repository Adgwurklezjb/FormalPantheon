import Analysis.ContourCertificates.Outer.Block1216
import Analysis.ContourCertificates.Outer.Block1217
import Analysis.ContourCertificates.Outer.Block1218
import Analysis.ContourCertificates.Outer.Block1219
import Analysis.ContourCertificates.Outer.Block1220
import Analysis.ContourCertificates.Outer.Block1221
import Analysis.ContourCertificates.Outer.Block1222
import Analysis.ContourCertificates.Outer.Block1223

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch152

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1216.cells ++
  DirichletL.ContourCertificates.Outer.Block1217.cells ++
  DirichletL.ContourCertificates.Outer.Block1218.cells ++
  DirichletL.ContourCertificates.Outer.Block1219.cells ++
  DirichletL.ContourCertificates.Outer.Block1220.cells ++
  DirichletL.ContourCertificates.Outer.Block1221.cells ++
  DirichletL.ContourCertificates.Outer.Block1222.cells ++
  DirichletL.ContourCertificates.Outer.Block1223.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1216.cells_bounded, DirichletL.ContourCertificates.Outer.Block1217.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1218.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1219.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1220.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1221.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1222.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1223.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch152
