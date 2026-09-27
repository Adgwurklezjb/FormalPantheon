import Analysis.ContourCertificates.Outer.Block0968
import Analysis.ContourCertificates.Outer.Block0969
import Analysis.ContourCertificates.Outer.Block0970
import Analysis.ContourCertificates.Outer.Block0971
import Analysis.ContourCertificates.Outer.Block0972
import Analysis.ContourCertificates.Outer.Block0973
import Analysis.ContourCertificates.Outer.Block0974
import Analysis.ContourCertificates.Outer.Block0975

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch121

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0968.cells ++
  DirichletL.ContourCertificates.Outer.Block0969.cells ++
  DirichletL.ContourCertificates.Outer.Block0970.cells ++
  DirichletL.ContourCertificates.Outer.Block0971.cells ++
  DirichletL.ContourCertificates.Outer.Block0972.cells ++
  DirichletL.ContourCertificates.Outer.Block0973.cells ++
  DirichletL.ContourCertificates.Outer.Block0974.cells ++
  DirichletL.ContourCertificates.Outer.Block0975.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0968.cells_bounded, DirichletL.ContourCertificates.Outer.Block0969.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0970.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0971.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0972.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0973.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0974.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0975.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch121
