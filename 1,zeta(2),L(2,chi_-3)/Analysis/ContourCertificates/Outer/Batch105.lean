import Analysis.ContourCertificates.Outer.Block0840
import Analysis.ContourCertificates.Outer.Block0841
import Analysis.ContourCertificates.Outer.Block0842
import Analysis.ContourCertificates.Outer.Block0843
import Analysis.ContourCertificates.Outer.Block0844
import Analysis.ContourCertificates.Outer.Block0845
import Analysis.ContourCertificates.Outer.Block0846
import Analysis.ContourCertificates.Outer.Block0847

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch105

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0840.cells ++
  DirichletL.ContourCertificates.Outer.Block0841.cells ++
  DirichletL.ContourCertificates.Outer.Block0842.cells ++
  DirichletL.ContourCertificates.Outer.Block0843.cells ++
  DirichletL.ContourCertificates.Outer.Block0844.cells ++
  DirichletL.ContourCertificates.Outer.Block0845.cells ++
  DirichletL.ContourCertificates.Outer.Block0846.cells ++
  DirichletL.ContourCertificates.Outer.Block0847.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0840.cells_bounded, DirichletL.ContourCertificates.Outer.Block0841.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0842.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0843.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0844.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0845.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0846.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0847.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch105
