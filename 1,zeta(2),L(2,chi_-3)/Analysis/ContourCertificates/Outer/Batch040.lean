import Analysis.ContourCertificates.Outer.Block0320
import Analysis.ContourCertificates.Outer.Block0321
import Analysis.ContourCertificates.Outer.Block0322
import Analysis.ContourCertificates.Outer.Block0323
import Analysis.ContourCertificates.Outer.Block0324
import Analysis.ContourCertificates.Outer.Block0325
import Analysis.ContourCertificates.Outer.Block0326
import Analysis.ContourCertificates.Outer.Block0327

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch040

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0320.cells ++
  DirichletL.ContourCertificates.Outer.Block0321.cells ++
  DirichletL.ContourCertificates.Outer.Block0322.cells ++
  DirichletL.ContourCertificates.Outer.Block0323.cells ++
  DirichletL.ContourCertificates.Outer.Block0324.cells ++
  DirichletL.ContourCertificates.Outer.Block0325.cells ++
  DirichletL.ContourCertificates.Outer.Block0326.cells ++
  DirichletL.ContourCertificates.Outer.Block0327.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0320.cells_bounded, DirichletL.ContourCertificates.Outer.Block0321.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0322.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0323.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0324.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0325.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0326.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0327.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch040
