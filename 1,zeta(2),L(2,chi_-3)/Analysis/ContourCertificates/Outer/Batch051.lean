import Analysis.ContourCertificates.Outer.Block0408
import Analysis.ContourCertificates.Outer.Block0409
import Analysis.ContourCertificates.Outer.Block0410
import Analysis.ContourCertificates.Outer.Block0411
import Analysis.ContourCertificates.Outer.Block0412
import Analysis.ContourCertificates.Outer.Block0413
import Analysis.ContourCertificates.Outer.Block0414
import Analysis.ContourCertificates.Outer.Block0415

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch051

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0408.cells ++
  DirichletL.ContourCertificates.Outer.Block0409.cells ++
  DirichletL.ContourCertificates.Outer.Block0410.cells ++
  DirichletL.ContourCertificates.Outer.Block0411.cells ++
  DirichletL.ContourCertificates.Outer.Block0412.cells ++
  DirichletL.ContourCertificates.Outer.Block0413.cells ++
  DirichletL.ContourCertificates.Outer.Block0414.cells ++
  DirichletL.ContourCertificates.Outer.Block0415.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0408.cells_bounded, DirichletL.ContourCertificates.Outer.Block0409.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0410.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0411.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0412.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0413.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0414.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0415.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch051
