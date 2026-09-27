import Analysis.ContourCertificates.Outer.Block1024
import Analysis.ContourCertificates.Outer.Block1025
import Analysis.ContourCertificates.Outer.Block1026
import Analysis.ContourCertificates.Outer.Block1027
import Analysis.ContourCertificates.Outer.Block1028
import Analysis.ContourCertificates.Outer.Block1029
import Analysis.ContourCertificates.Outer.Block1030
import Analysis.ContourCertificates.Outer.Block1031

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch128

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1024.cells ++
  DirichletL.ContourCertificates.Outer.Block1025.cells ++
  DirichletL.ContourCertificates.Outer.Block1026.cells ++
  DirichletL.ContourCertificates.Outer.Block1027.cells ++
  DirichletL.ContourCertificates.Outer.Block1028.cells ++
  DirichletL.ContourCertificates.Outer.Block1029.cells ++
  DirichletL.ContourCertificates.Outer.Block1030.cells ++
  DirichletL.ContourCertificates.Outer.Block1031.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1024.cells_bounded, DirichletL.ContourCertificates.Outer.Block1025.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1026.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1027.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1028.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1029.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1030.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1031.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch128
