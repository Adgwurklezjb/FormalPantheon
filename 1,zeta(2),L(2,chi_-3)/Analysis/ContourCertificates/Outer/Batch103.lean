import Analysis.ContourCertificates.Outer.Block0824
import Analysis.ContourCertificates.Outer.Block0825
import Analysis.ContourCertificates.Outer.Block0826
import Analysis.ContourCertificates.Outer.Block0827
import Analysis.ContourCertificates.Outer.Block0828
import Analysis.ContourCertificates.Outer.Block0829
import Analysis.ContourCertificates.Outer.Block0830
import Analysis.ContourCertificates.Outer.Block0831

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch103

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0824.cells ++
  DirichletL.ContourCertificates.Outer.Block0825.cells ++
  DirichletL.ContourCertificates.Outer.Block0826.cells ++
  DirichletL.ContourCertificates.Outer.Block0827.cells ++
  DirichletL.ContourCertificates.Outer.Block0828.cells ++
  DirichletL.ContourCertificates.Outer.Block0829.cells ++
  DirichletL.ContourCertificates.Outer.Block0830.cells ++
  DirichletL.ContourCertificates.Outer.Block0831.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0824.cells_bounded, DirichletL.ContourCertificates.Outer.Block0825.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0826.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0827.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0828.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0829.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0830.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0831.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch103
