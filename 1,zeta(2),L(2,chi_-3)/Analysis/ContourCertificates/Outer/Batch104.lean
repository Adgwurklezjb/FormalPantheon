import Analysis.ContourCertificates.Outer.Block0832
import Analysis.ContourCertificates.Outer.Block0833
import Analysis.ContourCertificates.Outer.Block0834
import Analysis.ContourCertificates.Outer.Block0835
import Analysis.ContourCertificates.Outer.Block0836
import Analysis.ContourCertificates.Outer.Block0837
import Analysis.ContourCertificates.Outer.Block0838
import Analysis.ContourCertificates.Outer.Block0839

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch104

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0832.cells ++
  DirichletL.ContourCertificates.Outer.Block0833.cells ++
  DirichletL.ContourCertificates.Outer.Block0834.cells ++
  DirichletL.ContourCertificates.Outer.Block0835.cells ++
  DirichletL.ContourCertificates.Outer.Block0836.cells ++
  DirichletL.ContourCertificates.Outer.Block0837.cells ++
  DirichletL.ContourCertificates.Outer.Block0838.cells ++
  DirichletL.ContourCertificates.Outer.Block0839.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0832.cells_bounded, DirichletL.ContourCertificates.Outer.Block0833.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0834.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0835.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0836.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0837.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0838.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0839.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch104
