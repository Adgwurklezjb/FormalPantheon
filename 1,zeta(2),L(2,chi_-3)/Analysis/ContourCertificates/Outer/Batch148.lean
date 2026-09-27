import Analysis.ContourCertificates.Outer.Block1184
import Analysis.ContourCertificates.Outer.Block1185
import Analysis.ContourCertificates.Outer.Block1186
import Analysis.ContourCertificates.Outer.Block1187
import Analysis.ContourCertificates.Outer.Block1188
import Analysis.ContourCertificates.Outer.Block1189
import Analysis.ContourCertificates.Outer.Block1190
import Analysis.ContourCertificates.Outer.Block1191

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch148

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1184.cells ++
  DirichletL.ContourCertificates.Outer.Block1185.cells ++
  DirichletL.ContourCertificates.Outer.Block1186.cells ++
  DirichletL.ContourCertificates.Outer.Block1187.cells ++
  DirichletL.ContourCertificates.Outer.Block1188.cells ++
  DirichletL.ContourCertificates.Outer.Block1189.cells ++
  DirichletL.ContourCertificates.Outer.Block1190.cells ++
  DirichletL.ContourCertificates.Outer.Block1191.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1184.cells_bounded, DirichletL.ContourCertificates.Outer.Block1185.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1186.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1187.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1188.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1189.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1190.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1191.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch148
