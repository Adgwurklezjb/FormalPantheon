import Analysis.ContourCertificates.Outer.Block0896
import Analysis.ContourCertificates.Outer.Block0897
import Analysis.ContourCertificates.Outer.Block0898
import Analysis.ContourCertificates.Outer.Block0899
import Analysis.ContourCertificates.Outer.Block0900
import Analysis.ContourCertificates.Outer.Block0901
import Analysis.ContourCertificates.Outer.Block0902
import Analysis.ContourCertificates.Outer.Block0903

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch112

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0896.cells ++
  DirichletL.ContourCertificates.Outer.Block0897.cells ++
  DirichletL.ContourCertificates.Outer.Block0898.cells ++
  DirichletL.ContourCertificates.Outer.Block0899.cells ++
  DirichletL.ContourCertificates.Outer.Block0900.cells ++
  DirichletL.ContourCertificates.Outer.Block0901.cells ++
  DirichletL.ContourCertificates.Outer.Block0902.cells ++
  DirichletL.ContourCertificates.Outer.Block0903.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0896.cells_bounded, DirichletL.ContourCertificates.Outer.Block0897.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0898.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0899.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0900.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0901.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0902.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0903.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch112
