import Analysis.ContourCertificates.Outer.Block0744
import Analysis.ContourCertificates.Outer.Block0745
import Analysis.ContourCertificates.Outer.Block0746
import Analysis.ContourCertificates.Outer.Block0747
import Analysis.ContourCertificates.Outer.Block0748
import Analysis.ContourCertificates.Outer.Block0749
import Analysis.ContourCertificates.Outer.Block0750
import Analysis.ContourCertificates.Outer.Block0751

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch093

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0744.cells ++
  DirichletL.ContourCertificates.Outer.Block0745.cells ++
  DirichletL.ContourCertificates.Outer.Block0746.cells ++
  DirichletL.ContourCertificates.Outer.Block0747.cells ++
  DirichletL.ContourCertificates.Outer.Block0748.cells ++
  DirichletL.ContourCertificates.Outer.Block0749.cells ++
  DirichletL.ContourCertificates.Outer.Block0750.cells ++
  DirichletL.ContourCertificates.Outer.Block0751.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0744.cells_bounded, DirichletL.ContourCertificates.Outer.Block0745.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0746.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0747.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0748.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0749.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0750.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0751.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch093
