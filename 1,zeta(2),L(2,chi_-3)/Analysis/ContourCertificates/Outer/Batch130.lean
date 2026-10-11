import Analysis.ContourCertificates.Outer.Block1040
import Analysis.ContourCertificates.Outer.Block1041
import Analysis.ContourCertificates.Outer.Block1042
import Analysis.ContourCertificates.Outer.Block1043
import Analysis.ContourCertificates.Outer.Block1044
import Analysis.ContourCertificates.Outer.Block1045
import Analysis.ContourCertificates.Outer.Block1046
import Analysis.ContourCertificates.Outer.Block1047

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch130

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1040.cells ++
  DirichletL.ContourCertificates.Outer.Block1041.cells ++
  DirichletL.ContourCertificates.Outer.Block1042.cells ++
  DirichletL.ContourCertificates.Outer.Block1043.cells ++
  DirichletL.ContourCertificates.Outer.Block1044.cells ++
  DirichletL.ContourCertificates.Outer.Block1045.cells ++
  DirichletL.ContourCertificates.Outer.Block1046.cells ++
  DirichletL.ContourCertificates.Outer.Block1047.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1040.cells_bounded, DirichletL.ContourCertificates.Outer.Block1041.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1042.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1043.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1044.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1045.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1046.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1047.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch130
