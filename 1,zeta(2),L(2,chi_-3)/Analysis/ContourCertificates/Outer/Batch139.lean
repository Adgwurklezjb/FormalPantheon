import Analysis.ContourCertificates.Outer.Block1112
import Analysis.ContourCertificates.Outer.Block1113
import Analysis.ContourCertificates.Outer.Block1114
import Analysis.ContourCertificates.Outer.Block1115
import Analysis.ContourCertificates.Outer.Block1116
import Analysis.ContourCertificates.Outer.Block1117
import Analysis.ContourCertificates.Outer.Block1118
import Analysis.ContourCertificates.Outer.Block1119

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch139

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1112.cells ++
  DirichletL.ContourCertificates.Outer.Block1113.cells ++
  DirichletL.ContourCertificates.Outer.Block1114.cells ++
  DirichletL.ContourCertificates.Outer.Block1115.cells ++
  DirichletL.ContourCertificates.Outer.Block1116.cells ++
  DirichletL.ContourCertificates.Outer.Block1117.cells ++
  DirichletL.ContourCertificates.Outer.Block1118.cells ++
  DirichletL.ContourCertificates.Outer.Block1119.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1112.cells_bounded, DirichletL.ContourCertificates.Outer.Block1113.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1114.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1115.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1116.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1117.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1118.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1119.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch139
