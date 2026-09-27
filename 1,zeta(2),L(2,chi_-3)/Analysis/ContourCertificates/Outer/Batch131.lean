import Analysis.ContourCertificates.Outer.Block1048
import Analysis.ContourCertificates.Outer.Block1049
import Analysis.ContourCertificates.Outer.Block1050
import Analysis.ContourCertificates.Outer.Block1051
import Analysis.ContourCertificates.Outer.Block1052
import Analysis.ContourCertificates.Outer.Block1053
import Analysis.ContourCertificates.Outer.Block1054
import Analysis.ContourCertificates.Outer.Block1055

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch131

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1048.cells ++
  DirichletL.ContourCertificates.Outer.Block1049.cells ++
  DirichletL.ContourCertificates.Outer.Block1050.cells ++
  DirichletL.ContourCertificates.Outer.Block1051.cells ++
  DirichletL.ContourCertificates.Outer.Block1052.cells ++
  DirichletL.ContourCertificates.Outer.Block1053.cells ++
  DirichletL.ContourCertificates.Outer.Block1054.cells ++
  DirichletL.ContourCertificates.Outer.Block1055.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1048.cells_bounded, DirichletL.ContourCertificates.Outer.Block1049.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1050.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1051.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1052.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1053.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1054.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1055.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch131
