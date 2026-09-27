import Analysis.ContourCertificates.Outer.Block0264
import Analysis.ContourCertificates.Outer.Block0265
import Analysis.ContourCertificates.Outer.Block0266
import Analysis.ContourCertificates.Outer.Block0267
import Analysis.ContourCertificates.Outer.Block0268
import Analysis.ContourCertificates.Outer.Block0269
import Analysis.ContourCertificates.Outer.Block0270
import Analysis.ContourCertificates.Outer.Block0271

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch033

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0264.cells ++
  DirichletL.ContourCertificates.Outer.Block0265.cells ++
  DirichletL.ContourCertificates.Outer.Block0266.cells ++
  DirichletL.ContourCertificates.Outer.Block0267.cells ++
  DirichletL.ContourCertificates.Outer.Block0268.cells ++
  DirichletL.ContourCertificates.Outer.Block0269.cells ++
  DirichletL.ContourCertificates.Outer.Block0270.cells ++
  DirichletL.ContourCertificates.Outer.Block0271.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0264.cells_bounded, DirichletL.ContourCertificates.Outer.Block0265.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0266.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0267.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0268.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0269.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0270.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0271.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch033
