import Analysis.ContourCertificates.Outer.Block0760
import Analysis.ContourCertificates.Outer.Block0761
import Analysis.ContourCertificates.Outer.Block0762
import Analysis.ContourCertificates.Outer.Block0763
import Analysis.ContourCertificates.Outer.Block0764
import Analysis.ContourCertificates.Outer.Block0765
import Analysis.ContourCertificates.Outer.Block0766
import Analysis.ContourCertificates.Outer.Block0767

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch095

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0760.cells ++
  DirichletL.ContourCertificates.Outer.Block0761.cells ++
  DirichletL.ContourCertificates.Outer.Block0762.cells ++
  DirichletL.ContourCertificates.Outer.Block0763.cells ++
  DirichletL.ContourCertificates.Outer.Block0764.cells ++
  DirichletL.ContourCertificates.Outer.Block0765.cells ++
  DirichletL.ContourCertificates.Outer.Block0766.cells ++
  DirichletL.ContourCertificates.Outer.Block0767.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0760.cells_bounded, DirichletL.ContourCertificates.Outer.Block0761.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0762.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0763.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0764.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0765.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0766.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0767.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch095
