import Analysis.ContourCertificates.Outer.Block0472
import Analysis.ContourCertificates.Outer.Block0473
import Analysis.ContourCertificates.Outer.Block0474
import Analysis.ContourCertificates.Outer.Block0475
import Analysis.ContourCertificates.Outer.Block0476
import Analysis.ContourCertificates.Outer.Block0477
import Analysis.ContourCertificates.Outer.Block0478
import Analysis.ContourCertificates.Outer.Block0479

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch059

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0472.cells ++
  DirichletL.ContourCertificates.Outer.Block0473.cells ++
  DirichletL.ContourCertificates.Outer.Block0474.cells ++
  DirichletL.ContourCertificates.Outer.Block0475.cells ++
  DirichletL.ContourCertificates.Outer.Block0476.cells ++
  DirichletL.ContourCertificates.Outer.Block0477.cells ++
  DirichletL.ContourCertificates.Outer.Block0478.cells ++
  DirichletL.ContourCertificates.Outer.Block0479.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0472.cells_bounded, DirichletL.ContourCertificates.Outer.Block0473.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0474.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0475.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0476.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0477.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0478.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0479.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch059
