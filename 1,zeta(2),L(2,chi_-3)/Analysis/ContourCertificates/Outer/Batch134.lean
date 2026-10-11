import Analysis.ContourCertificates.Outer.Block1072
import Analysis.ContourCertificates.Outer.Block1073
import Analysis.ContourCertificates.Outer.Block1074
import Analysis.ContourCertificates.Outer.Block1075
import Analysis.ContourCertificates.Outer.Block1076
import Analysis.ContourCertificates.Outer.Block1077
import Analysis.ContourCertificates.Outer.Block1078
import Analysis.ContourCertificates.Outer.Block1079

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch134

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1072.cells ++
  DirichletL.ContourCertificates.Outer.Block1073.cells ++
  DirichletL.ContourCertificates.Outer.Block1074.cells ++
  DirichletL.ContourCertificates.Outer.Block1075.cells ++
  DirichletL.ContourCertificates.Outer.Block1076.cells ++
  DirichletL.ContourCertificates.Outer.Block1077.cells ++
  DirichletL.ContourCertificates.Outer.Block1078.cells ++
  DirichletL.ContourCertificates.Outer.Block1079.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1072.cells_bounded, DirichletL.ContourCertificates.Outer.Block1073.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1074.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1075.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1076.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1077.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1078.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1079.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch134
