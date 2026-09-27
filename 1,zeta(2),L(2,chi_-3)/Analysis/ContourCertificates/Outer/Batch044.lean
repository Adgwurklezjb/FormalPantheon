import Analysis.ContourCertificates.Outer.Block0352
import Analysis.ContourCertificates.Outer.Block0353
import Analysis.ContourCertificates.Outer.Block0354
import Analysis.ContourCertificates.Outer.Block0355
import Analysis.ContourCertificates.Outer.Block0356
import Analysis.ContourCertificates.Outer.Block0357
import Analysis.ContourCertificates.Outer.Block0358
import Analysis.ContourCertificates.Outer.Block0359

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch044

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0352.cells ++
  DirichletL.ContourCertificates.Outer.Block0353.cells ++
  DirichletL.ContourCertificates.Outer.Block0354.cells ++
  DirichletL.ContourCertificates.Outer.Block0355.cells ++
  DirichletL.ContourCertificates.Outer.Block0356.cells ++
  DirichletL.ContourCertificates.Outer.Block0357.cells ++
  DirichletL.ContourCertificates.Outer.Block0358.cells ++
  DirichletL.ContourCertificates.Outer.Block0359.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0352.cells_bounded, DirichletL.ContourCertificates.Outer.Block0353.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0354.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0355.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0356.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0357.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0358.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0359.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch044
