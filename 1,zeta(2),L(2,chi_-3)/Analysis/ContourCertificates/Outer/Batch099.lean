import Analysis.ContourCertificates.Outer.Block0792
import Analysis.ContourCertificates.Outer.Block0793
import Analysis.ContourCertificates.Outer.Block0794
import Analysis.ContourCertificates.Outer.Block0795
import Analysis.ContourCertificates.Outer.Block0796
import Analysis.ContourCertificates.Outer.Block0797
import Analysis.ContourCertificates.Outer.Block0798
import Analysis.ContourCertificates.Outer.Block0799

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch099

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0792.cells ++
  DirichletL.ContourCertificates.Outer.Block0793.cells ++
  DirichletL.ContourCertificates.Outer.Block0794.cells ++
  DirichletL.ContourCertificates.Outer.Block0795.cells ++
  DirichletL.ContourCertificates.Outer.Block0796.cells ++
  DirichletL.ContourCertificates.Outer.Block0797.cells ++
  DirichletL.ContourCertificates.Outer.Block0798.cells ++
  DirichletL.ContourCertificates.Outer.Block0799.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0792.cells_bounded, DirichletL.ContourCertificates.Outer.Block0793.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0794.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0795.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0796.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0797.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0798.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0799.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch099
