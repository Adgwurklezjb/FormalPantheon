import Analysis.ContourCertificates.Outer.Block0024
import Analysis.ContourCertificates.Outer.Block0025
import Analysis.ContourCertificates.Outer.Block0026
import Analysis.ContourCertificates.Outer.Block0027
import Analysis.ContourCertificates.Outer.Block0028
import Analysis.ContourCertificates.Outer.Block0029
import Analysis.ContourCertificates.Outer.Block0030
import Analysis.ContourCertificates.Outer.Block0031

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch003

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0024.cells ++
  DirichletL.ContourCertificates.Outer.Block0025.cells ++
  DirichletL.ContourCertificates.Outer.Block0026.cells ++
  DirichletL.ContourCertificates.Outer.Block0027.cells ++
  DirichletL.ContourCertificates.Outer.Block0028.cells ++
  DirichletL.ContourCertificates.Outer.Block0029.cells ++
  DirichletL.ContourCertificates.Outer.Block0030.cells ++
  DirichletL.ContourCertificates.Outer.Block0031.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0024.cells_bounded, DirichletL.ContourCertificates.Outer.Block0025.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0026.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0027.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0028.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0029.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0030.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0031.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch003
