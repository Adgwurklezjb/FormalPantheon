import Analysis.ContourCertificates.Outer.Block0224
import Analysis.ContourCertificates.Outer.Block0225
import Analysis.ContourCertificates.Outer.Block0226
import Analysis.ContourCertificates.Outer.Block0227
import Analysis.ContourCertificates.Outer.Block0228
import Analysis.ContourCertificates.Outer.Block0229
import Analysis.ContourCertificates.Outer.Block0230
import Analysis.ContourCertificates.Outer.Block0231

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch028

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0224.cells ++
  DirichletL.ContourCertificates.Outer.Block0225.cells ++
  DirichletL.ContourCertificates.Outer.Block0226.cells ++
  DirichletL.ContourCertificates.Outer.Block0227.cells ++
  DirichletL.ContourCertificates.Outer.Block0228.cells ++
  DirichletL.ContourCertificates.Outer.Block0229.cells ++
  DirichletL.ContourCertificates.Outer.Block0230.cells ++
  DirichletL.ContourCertificates.Outer.Block0231.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0224.cells_bounded, DirichletL.ContourCertificates.Outer.Block0225.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0226.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0227.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0228.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0229.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0230.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0231.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch028
