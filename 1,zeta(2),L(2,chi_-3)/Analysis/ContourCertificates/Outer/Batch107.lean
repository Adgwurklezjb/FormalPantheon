import Analysis.ContourCertificates.Outer.Block0856
import Analysis.ContourCertificates.Outer.Block0857
import Analysis.ContourCertificates.Outer.Block0858
import Analysis.ContourCertificates.Outer.Block0859
import Analysis.ContourCertificates.Outer.Block0860
import Analysis.ContourCertificates.Outer.Block0861
import Analysis.ContourCertificates.Outer.Block0862
import Analysis.ContourCertificates.Outer.Block0863

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch107

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0856.cells ++
  DirichletL.ContourCertificates.Outer.Block0857.cells ++
  DirichletL.ContourCertificates.Outer.Block0858.cells ++
  DirichletL.ContourCertificates.Outer.Block0859.cells ++
  DirichletL.ContourCertificates.Outer.Block0860.cells ++
  DirichletL.ContourCertificates.Outer.Block0861.cells ++
  DirichletL.ContourCertificates.Outer.Block0862.cells ++
  DirichletL.ContourCertificates.Outer.Block0863.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0856.cells_bounded, DirichletL.ContourCertificates.Outer.Block0857.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0858.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0859.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0860.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0861.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0862.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0863.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch107
