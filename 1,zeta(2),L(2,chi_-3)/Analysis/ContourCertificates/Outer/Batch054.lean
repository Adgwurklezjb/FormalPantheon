import Analysis.ContourCertificates.Outer.Block0432
import Analysis.ContourCertificates.Outer.Block0433
import Analysis.ContourCertificates.Outer.Block0434
import Analysis.ContourCertificates.Outer.Block0435
import Analysis.ContourCertificates.Outer.Block0436
import Analysis.ContourCertificates.Outer.Block0437
import Analysis.ContourCertificates.Outer.Block0438
import Analysis.ContourCertificates.Outer.Block0439

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch054

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0432.cells ++
  DirichletL.ContourCertificates.Outer.Block0433.cells ++
  DirichletL.ContourCertificates.Outer.Block0434.cells ++
  DirichletL.ContourCertificates.Outer.Block0435.cells ++
  DirichletL.ContourCertificates.Outer.Block0436.cells ++
  DirichletL.ContourCertificates.Outer.Block0437.cells ++
  DirichletL.ContourCertificates.Outer.Block0438.cells ++
  DirichletL.ContourCertificates.Outer.Block0439.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0432.cells_bounded, DirichletL.ContourCertificates.Outer.Block0433.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0434.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0435.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0436.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0437.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0438.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0439.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch054
