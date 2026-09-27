import Analysis.ContourCertificates.Outer.Block0872
import Analysis.ContourCertificates.Outer.Block0873
import Analysis.ContourCertificates.Outer.Block0874
import Analysis.ContourCertificates.Outer.Block0875
import Analysis.ContourCertificates.Outer.Block0876
import Analysis.ContourCertificates.Outer.Block0877
import Analysis.ContourCertificates.Outer.Block0878
import Analysis.ContourCertificates.Outer.Block0879

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch109

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0872.cells ++
  DirichletL.ContourCertificates.Outer.Block0873.cells ++
  DirichletL.ContourCertificates.Outer.Block0874.cells ++
  DirichletL.ContourCertificates.Outer.Block0875.cells ++
  DirichletL.ContourCertificates.Outer.Block0876.cells ++
  DirichletL.ContourCertificates.Outer.Block0877.cells ++
  DirichletL.ContourCertificates.Outer.Block0878.cells ++
  DirichletL.ContourCertificates.Outer.Block0879.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0872.cells_bounded, DirichletL.ContourCertificates.Outer.Block0873.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0874.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0875.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0876.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0877.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0878.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0879.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch109
