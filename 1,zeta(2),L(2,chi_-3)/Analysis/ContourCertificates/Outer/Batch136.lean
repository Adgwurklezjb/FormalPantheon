import Analysis.ContourCertificates.Outer.Block1088
import Analysis.ContourCertificates.Outer.Block1089
import Analysis.ContourCertificates.Outer.Block1090
import Analysis.ContourCertificates.Outer.Block1091
import Analysis.ContourCertificates.Outer.Block1092
import Analysis.ContourCertificates.Outer.Block1093
import Analysis.ContourCertificates.Outer.Block1094
import Analysis.ContourCertificates.Outer.Block1095

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch136

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1088.cells ++
  DirichletL.ContourCertificates.Outer.Block1089.cells ++
  DirichletL.ContourCertificates.Outer.Block1090.cells ++
  DirichletL.ContourCertificates.Outer.Block1091.cells ++
  DirichletL.ContourCertificates.Outer.Block1092.cells ++
  DirichletL.ContourCertificates.Outer.Block1093.cells ++
  DirichletL.ContourCertificates.Outer.Block1094.cells ++
  DirichletL.ContourCertificates.Outer.Block1095.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1088.cells_bounded, DirichletL.ContourCertificates.Outer.Block1089.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1090.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1091.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1092.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1093.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1094.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1095.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch136
