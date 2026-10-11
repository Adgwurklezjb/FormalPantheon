import Analysis.ContourCertificates.Outer.Block0648
import Analysis.ContourCertificates.Outer.Block0649
import Analysis.ContourCertificates.Outer.Block0650
import Analysis.ContourCertificates.Outer.Block0651
import Analysis.ContourCertificates.Outer.Block0652
import Analysis.ContourCertificates.Outer.Block0653
import Analysis.ContourCertificates.Outer.Block0654
import Analysis.ContourCertificates.Outer.Block0655

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch081

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0648.cells ++
  DirichletL.ContourCertificates.Outer.Block0649.cells ++
  DirichletL.ContourCertificates.Outer.Block0650.cells ++
  DirichletL.ContourCertificates.Outer.Block0651.cells ++
  DirichletL.ContourCertificates.Outer.Block0652.cells ++
  DirichletL.ContourCertificates.Outer.Block0653.cells ++
  DirichletL.ContourCertificates.Outer.Block0654.cells ++
  DirichletL.ContourCertificates.Outer.Block0655.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0648.cells_bounded, DirichletL.ContourCertificates.Outer.Block0649.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0650.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0651.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0652.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0653.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0654.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0655.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch081
