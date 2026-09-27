import Analysis.ContourCertificates.Outer.Block0296
import Analysis.ContourCertificates.Outer.Block0297
import Analysis.ContourCertificates.Outer.Block0298
import Analysis.ContourCertificates.Outer.Block0299
import Analysis.ContourCertificates.Outer.Block0300
import Analysis.ContourCertificates.Outer.Block0301
import Analysis.ContourCertificates.Outer.Block0302
import Analysis.ContourCertificates.Outer.Block0303

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch037

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0296.cells ++
  DirichletL.ContourCertificates.Outer.Block0297.cells ++
  DirichletL.ContourCertificates.Outer.Block0298.cells ++
  DirichletL.ContourCertificates.Outer.Block0299.cells ++
  DirichletL.ContourCertificates.Outer.Block0300.cells ++
  DirichletL.ContourCertificates.Outer.Block0301.cells ++
  DirichletL.ContourCertificates.Outer.Block0302.cells ++
  DirichletL.ContourCertificates.Outer.Block0303.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0296.cells_bounded, DirichletL.ContourCertificates.Outer.Block0297.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0298.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0299.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0300.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0301.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0302.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0303.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch037
