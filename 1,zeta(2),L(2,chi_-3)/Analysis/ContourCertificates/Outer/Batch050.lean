import Analysis.ContourCertificates.Outer.Block0400
import Analysis.ContourCertificates.Outer.Block0401
import Analysis.ContourCertificates.Outer.Block0402
import Analysis.ContourCertificates.Outer.Block0403
import Analysis.ContourCertificates.Outer.Block0404
import Analysis.ContourCertificates.Outer.Block0405
import Analysis.ContourCertificates.Outer.Block0406
import Analysis.ContourCertificates.Outer.Block0407

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch050

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0400.cells ++
  DirichletL.ContourCertificates.Outer.Block0401.cells ++
  DirichletL.ContourCertificates.Outer.Block0402.cells ++
  DirichletL.ContourCertificates.Outer.Block0403.cells ++
  DirichletL.ContourCertificates.Outer.Block0404.cells ++
  DirichletL.ContourCertificates.Outer.Block0405.cells ++
  DirichletL.ContourCertificates.Outer.Block0406.cells ++
  DirichletL.ContourCertificates.Outer.Block0407.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0400.cells_bounded, DirichletL.ContourCertificates.Outer.Block0401.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0402.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0403.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0404.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0405.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0406.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0407.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch050
