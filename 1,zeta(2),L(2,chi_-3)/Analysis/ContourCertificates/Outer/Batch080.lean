import Analysis.ContourCertificates.Outer.Block0640
import Analysis.ContourCertificates.Outer.Block0641
import Analysis.ContourCertificates.Outer.Block0642
import Analysis.ContourCertificates.Outer.Block0643
import Analysis.ContourCertificates.Outer.Block0644
import Analysis.ContourCertificates.Outer.Block0645
import Analysis.ContourCertificates.Outer.Block0646
import Analysis.ContourCertificates.Outer.Block0647

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch080

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0640.cells ++
  DirichletL.ContourCertificates.Outer.Block0641.cells ++
  DirichletL.ContourCertificates.Outer.Block0642.cells ++
  DirichletL.ContourCertificates.Outer.Block0643.cells ++
  DirichletL.ContourCertificates.Outer.Block0644.cells ++
  DirichletL.ContourCertificates.Outer.Block0645.cells ++
  DirichletL.ContourCertificates.Outer.Block0646.cells ++
  DirichletL.ContourCertificates.Outer.Block0647.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0640.cells_bounded, DirichletL.ContourCertificates.Outer.Block0641.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0642.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0643.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0644.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0645.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0646.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0647.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch080
