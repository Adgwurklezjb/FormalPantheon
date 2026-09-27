import Analysis.ContourCertificates.Outer.Block0112
import Analysis.ContourCertificates.Outer.Block0113
import Analysis.ContourCertificates.Outer.Block0114
import Analysis.ContourCertificates.Outer.Block0115
import Analysis.ContourCertificates.Outer.Block0116
import Analysis.ContourCertificates.Outer.Block0117
import Analysis.ContourCertificates.Outer.Block0118
import Analysis.ContourCertificates.Outer.Block0119

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch014

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0112.cells ++
  DirichletL.ContourCertificates.Outer.Block0113.cells ++
  DirichletL.ContourCertificates.Outer.Block0114.cells ++
  DirichletL.ContourCertificates.Outer.Block0115.cells ++
  DirichletL.ContourCertificates.Outer.Block0116.cells ++
  DirichletL.ContourCertificates.Outer.Block0117.cells ++
  DirichletL.ContourCertificates.Outer.Block0118.cells ++
  DirichletL.ContourCertificates.Outer.Block0119.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0112.cells_bounded, DirichletL.ContourCertificates.Outer.Block0113.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0114.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0115.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0116.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0117.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0118.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0119.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch014
