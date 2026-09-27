import Analysis.ContourCertificates.Outer.Block0672
import Analysis.ContourCertificates.Outer.Block0673
import Analysis.ContourCertificates.Outer.Block0674
import Analysis.ContourCertificates.Outer.Block0675
import Analysis.ContourCertificates.Outer.Block0676
import Analysis.ContourCertificates.Outer.Block0677
import Analysis.ContourCertificates.Outer.Block0678
import Analysis.ContourCertificates.Outer.Block0679

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch084

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0672.cells ++
  DirichletL.ContourCertificates.Outer.Block0673.cells ++
  DirichletL.ContourCertificates.Outer.Block0674.cells ++
  DirichletL.ContourCertificates.Outer.Block0675.cells ++
  DirichletL.ContourCertificates.Outer.Block0676.cells ++
  DirichletL.ContourCertificates.Outer.Block0677.cells ++
  DirichletL.ContourCertificates.Outer.Block0678.cells ++
  DirichletL.ContourCertificates.Outer.Block0679.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0672.cells_bounded, DirichletL.ContourCertificates.Outer.Block0673.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0674.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0675.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0676.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0677.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0678.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0679.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch084
