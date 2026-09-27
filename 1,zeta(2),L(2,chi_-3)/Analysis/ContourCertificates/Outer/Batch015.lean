import Analysis.ContourCertificates.Outer.Block0120
import Analysis.ContourCertificates.Outer.Block0121
import Analysis.ContourCertificates.Outer.Block0122
import Analysis.ContourCertificates.Outer.Block0123
import Analysis.ContourCertificates.Outer.Block0124
import Analysis.ContourCertificates.Outer.Block0125
import Analysis.ContourCertificates.Outer.Block0126
import Analysis.ContourCertificates.Outer.Block0127

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch015

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0120.cells ++
  DirichletL.ContourCertificates.Outer.Block0121.cells ++
  DirichletL.ContourCertificates.Outer.Block0122.cells ++
  DirichletL.ContourCertificates.Outer.Block0123.cells ++
  DirichletL.ContourCertificates.Outer.Block0124.cells ++
  DirichletL.ContourCertificates.Outer.Block0125.cells ++
  DirichletL.ContourCertificates.Outer.Block0126.cells ++
  DirichletL.ContourCertificates.Outer.Block0127.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0120.cells_bounded, DirichletL.ContourCertificates.Outer.Block0121.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0122.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0123.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0124.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0125.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0126.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0127.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch015
