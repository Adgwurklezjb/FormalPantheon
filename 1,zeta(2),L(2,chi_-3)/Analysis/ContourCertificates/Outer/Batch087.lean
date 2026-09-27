import Analysis.ContourCertificates.Outer.Block0696
import Analysis.ContourCertificates.Outer.Block0697
import Analysis.ContourCertificates.Outer.Block0698
import Analysis.ContourCertificates.Outer.Block0699
import Analysis.ContourCertificates.Outer.Block0700
import Analysis.ContourCertificates.Outer.Block0701
import Analysis.ContourCertificates.Outer.Block0702
import Analysis.ContourCertificates.Outer.Block0703

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch087

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0696.cells ++
  DirichletL.ContourCertificates.Outer.Block0697.cells ++
  DirichletL.ContourCertificates.Outer.Block0698.cells ++
  DirichletL.ContourCertificates.Outer.Block0699.cells ++
  DirichletL.ContourCertificates.Outer.Block0700.cells ++
  DirichletL.ContourCertificates.Outer.Block0701.cells ++
  DirichletL.ContourCertificates.Outer.Block0702.cells ++
  DirichletL.ContourCertificates.Outer.Block0703.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0696.cells_bounded, DirichletL.ContourCertificates.Outer.Block0697.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0698.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0699.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0700.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0701.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0702.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0703.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch087
