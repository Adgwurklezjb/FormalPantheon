import Analysis.ContourCertificates.Outer.Block0920
import Analysis.ContourCertificates.Outer.Block0921
import Analysis.ContourCertificates.Outer.Block0922
import Analysis.ContourCertificates.Outer.Block0923
import Analysis.ContourCertificates.Outer.Block0924
import Analysis.ContourCertificates.Outer.Block0925
import Analysis.ContourCertificates.Outer.Block0926
import Analysis.ContourCertificates.Outer.Block0927

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch115

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0920.cells ++
  DirichletL.ContourCertificates.Outer.Block0921.cells ++
  DirichletL.ContourCertificates.Outer.Block0922.cells ++
  DirichletL.ContourCertificates.Outer.Block0923.cells ++
  DirichletL.ContourCertificates.Outer.Block0924.cells ++
  DirichletL.ContourCertificates.Outer.Block0925.cells ++
  DirichletL.ContourCertificates.Outer.Block0926.cells ++
  DirichletL.ContourCertificates.Outer.Block0927.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0920.cells_bounded, DirichletL.ContourCertificates.Outer.Block0921.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0922.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0923.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0924.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0925.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0926.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0927.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch115
