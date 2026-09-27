import Analysis.ContourCertificates.Outer.Block0512
import Analysis.ContourCertificates.Outer.Block0513
import Analysis.ContourCertificates.Outer.Block0514
import Analysis.ContourCertificates.Outer.Block0515
import Analysis.ContourCertificates.Outer.Block0516
import Analysis.ContourCertificates.Outer.Block0517
import Analysis.ContourCertificates.Outer.Block0518
import Analysis.ContourCertificates.Outer.Block0519

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch064

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0512.cells ++
  DirichletL.ContourCertificates.Outer.Block0513.cells ++
  DirichletL.ContourCertificates.Outer.Block0514.cells ++
  DirichletL.ContourCertificates.Outer.Block0515.cells ++
  DirichletL.ContourCertificates.Outer.Block0516.cells ++
  DirichletL.ContourCertificates.Outer.Block0517.cells ++
  DirichletL.ContourCertificates.Outer.Block0518.cells ++
  DirichletL.ContourCertificates.Outer.Block0519.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0512.cells_bounded, DirichletL.ContourCertificates.Outer.Block0513.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0514.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0515.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0516.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0517.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0518.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0519.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch064
