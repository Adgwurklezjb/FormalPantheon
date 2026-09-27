import Analysis.ContourCertificates.Outer.Block0248
import Analysis.ContourCertificates.Outer.Block0249
import Analysis.ContourCertificates.Outer.Block0250
import Analysis.ContourCertificates.Outer.Block0251
import Analysis.ContourCertificates.Outer.Block0252
import Analysis.ContourCertificates.Outer.Block0253
import Analysis.ContourCertificates.Outer.Block0254
import Analysis.ContourCertificates.Outer.Block0255

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch031

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0248.cells ++
  DirichletL.ContourCertificates.Outer.Block0249.cells ++
  DirichletL.ContourCertificates.Outer.Block0250.cells ++
  DirichletL.ContourCertificates.Outer.Block0251.cells ++
  DirichletL.ContourCertificates.Outer.Block0252.cells ++
  DirichletL.ContourCertificates.Outer.Block0253.cells ++
  DirichletL.ContourCertificates.Outer.Block0254.cells ++
  DirichletL.ContourCertificates.Outer.Block0255.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0248.cells_bounded, DirichletL.ContourCertificates.Outer.Block0249.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0250.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0251.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0252.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0253.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0254.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0255.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch031
