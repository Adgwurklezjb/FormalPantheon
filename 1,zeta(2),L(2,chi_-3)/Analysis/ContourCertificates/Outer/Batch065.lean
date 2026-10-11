import Analysis.ContourCertificates.Outer.Block0520
import Analysis.ContourCertificates.Outer.Block0521
import Analysis.ContourCertificates.Outer.Block0522
import Analysis.ContourCertificates.Outer.Block0523
import Analysis.ContourCertificates.Outer.Block0524
import Analysis.ContourCertificates.Outer.Block0525
import Analysis.ContourCertificates.Outer.Block0526
import Analysis.ContourCertificates.Outer.Block0527

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch065

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0520.cells ++
  DirichletL.ContourCertificates.Outer.Block0521.cells ++
  DirichletL.ContourCertificates.Outer.Block0522.cells ++
  DirichletL.ContourCertificates.Outer.Block0523.cells ++
  DirichletL.ContourCertificates.Outer.Block0524.cells ++
  DirichletL.ContourCertificates.Outer.Block0525.cells ++
  DirichletL.ContourCertificates.Outer.Block0526.cells ++
  DirichletL.ContourCertificates.Outer.Block0527.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0520.cells_bounded, DirichletL.ContourCertificates.Outer.Block0521.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0522.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0523.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0524.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0525.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0526.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0527.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch065
