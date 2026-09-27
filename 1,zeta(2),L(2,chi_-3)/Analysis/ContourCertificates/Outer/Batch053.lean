import Analysis.ContourCertificates.Outer.Block0424
import Analysis.ContourCertificates.Outer.Block0425
import Analysis.ContourCertificates.Outer.Block0426
import Analysis.ContourCertificates.Outer.Block0427
import Analysis.ContourCertificates.Outer.Block0428
import Analysis.ContourCertificates.Outer.Block0429
import Analysis.ContourCertificates.Outer.Block0430
import Analysis.ContourCertificates.Outer.Block0431

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch053

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0424.cells ++
  DirichletL.ContourCertificates.Outer.Block0425.cells ++
  DirichletL.ContourCertificates.Outer.Block0426.cells ++
  DirichletL.ContourCertificates.Outer.Block0427.cells ++
  DirichletL.ContourCertificates.Outer.Block0428.cells ++
  DirichletL.ContourCertificates.Outer.Block0429.cells ++
  DirichletL.ContourCertificates.Outer.Block0430.cells ++
  DirichletL.ContourCertificates.Outer.Block0431.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0424.cells_bounded, DirichletL.ContourCertificates.Outer.Block0425.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0426.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0427.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0428.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0429.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0430.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0431.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch053
