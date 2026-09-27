import Analysis.ContourCertificates.Outer.Block1160
import Analysis.ContourCertificates.Outer.Block1161
import Analysis.ContourCertificates.Outer.Block1162
import Analysis.ContourCertificates.Outer.Block1163
import Analysis.ContourCertificates.Outer.Block1164
import Analysis.ContourCertificates.Outer.Block1165
import Analysis.ContourCertificates.Outer.Block1166
import Analysis.ContourCertificates.Outer.Block1167

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch145

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1160.cells ++
  DirichletL.ContourCertificates.Outer.Block1161.cells ++
  DirichletL.ContourCertificates.Outer.Block1162.cells ++
  DirichletL.ContourCertificates.Outer.Block1163.cells ++
  DirichletL.ContourCertificates.Outer.Block1164.cells ++
  DirichletL.ContourCertificates.Outer.Block1165.cells ++
  DirichletL.ContourCertificates.Outer.Block1166.cells ++
  DirichletL.ContourCertificates.Outer.Block1167.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1160.cells_bounded, DirichletL.ContourCertificates.Outer.Block1161.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1162.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1163.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1164.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1165.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1166.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1167.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch145
