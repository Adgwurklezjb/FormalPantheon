import Analysis.ContourCertificates.Outer.Block1144
import Analysis.ContourCertificates.Outer.Block1145
import Analysis.ContourCertificates.Outer.Block1146
import Analysis.ContourCertificates.Outer.Block1147
import Analysis.ContourCertificates.Outer.Block1148
import Analysis.ContourCertificates.Outer.Block1149
import Analysis.ContourCertificates.Outer.Block1150
import Analysis.ContourCertificates.Outer.Block1151

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch143

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1144.cells ++
  DirichletL.ContourCertificates.Outer.Block1145.cells ++
  DirichletL.ContourCertificates.Outer.Block1146.cells ++
  DirichletL.ContourCertificates.Outer.Block1147.cells ++
  DirichletL.ContourCertificates.Outer.Block1148.cells ++
  DirichletL.ContourCertificates.Outer.Block1149.cells ++
  DirichletL.ContourCertificates.Outer.Block1150.cells ++
  DirichletL.ContourCertificates.Outer.Block1151.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1144.cells_bounded, DirichletL.ContourCertificates.Outer.Block1145.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1146.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1147.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1148.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1149.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1150.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1151.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch143
