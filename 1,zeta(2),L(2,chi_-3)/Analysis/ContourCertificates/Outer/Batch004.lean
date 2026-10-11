import Analysis.ContourCertificates.Outer.Block0032
import Analysis.ContourCertificates.Outer.Block0033
import Analysis.ContourCertificates.Outer.Block0034
import Analysis.ContourCertificates.Outer.Block0035
import Analysis.ContourCertificates.Outer.Block0036
import Analysis.ContourCertificates.Outer.Block0037
import Analysis.ContourCertificates.Outer.Block0038
import Analysis.ContourCertificates.Outer.Block0039

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch004

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0032.cells ++
  DirichletL.ContourCertificates.Outer.Block0033.cells ++
  DirichletL.ContourCertificates.Outer.Block0034.cells ++
  DirichletL.ContourCertificates.Outer.Block0035.cells ++
  DirichletL.ContourCertificates.Outer.Block0036.cells ++
  DirichletL.ContourCertificates.Outer.Block0037.cells ++
  DirichletL.ContourCertificates.Outer.Block0038.cells ++
  DirichletL.ContourCertificates.Outer.Block0039.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0032.cells_bounded, DirichletL.ContourCertificates.Outer.Block0033.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0034.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0035.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0036.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0037.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0038.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0039.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch004
