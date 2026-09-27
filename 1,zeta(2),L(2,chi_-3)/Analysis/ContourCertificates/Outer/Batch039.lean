import Analysis.ContourCertificates.Outer.Block0312
import Analysis.ContourCertificates.Outer.Block0313
import Analysis.ContourCertificates.Outer.Block0314
import Analysis.ContourCertificates.Outer.Block0315
import Analysis.ContourCertificates.Outer.Block0316
import Analysis.ContourCertificates.Outer.Block0317
import Analysis.ContourCertificates.Outer.Block0318
import Analysis.ContourCertificates.Outer.Block0319

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch039

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0312.cells ++
  DirichletL.ContourCertificates.Outer.Block0313.cells ++
  DirichletL.ContourCertificates.Outer.Block0314.cells ++
  DirichletL.ContourCertificates.Outer.Block0315.cells ++
  DirichletL.ContourCertificates.Outer.Block0316.cells ++
  DirichletL.ContourCertificates.Outer.Block0317.cells ++
  DirichletL.ContourCertificates.Outer.Block0318.cells ++
  DirichletL.ContourCertificates.Outer.Block0319.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0312.cells_bounded, DirichletL.ContourCertificates.Outer.Block0313.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0314.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0315.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0316.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0317.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0318.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0319.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch039
