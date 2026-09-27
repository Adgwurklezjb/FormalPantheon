import Analysis.ContourCertificates.Outer.Block0344
import Analysis.ContourCertificates.Outer.Block0345
import Analysis.ContourCertificates.Outer.Block0346
import Analysis.ContourCertificates.Outer.Block0347
import Analysis.ContourCertificates.Outer.Block0348
import Analysis.ContourCertificates.Outer.Block0349
import Analysis.ContourCertificates.Outer.Block0350
import Analysis.ContourCertificates.Outer.Block0351

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch043

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0344.cells ++
  DirichletL.ContourCertificates.Outer.Block0345.cells ++
  DirichletL.ContourCertificates.Outer.Block0346.cells ++
  DirichletL.ContourCertificates.Outer.Block0347.cells ++
  DirichletL.ContourCertificates.Outer.Block0348.cells ++
  DirichletL.ContourCertificates.Outer.Block0349.cells ++
  DirichletL.ContourCertificates.Outer.Block0350.cells ++
  DirichletL.ContourCertificates.Outer.Block0351.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0344.cells_bounded, DirichletL.ContourCertificates.Outer.Block0345.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0346.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0347.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0348.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0349.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0350.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0351.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch043
