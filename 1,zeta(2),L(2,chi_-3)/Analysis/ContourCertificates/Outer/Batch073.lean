import Analysis.ContourCertificates.Outer.Block0584
import Analysis.ContourCertificates.Outer.Block0585
import Analysis.ContourCertificates.Outer.Block0586
import Analysis.ContourCertificates.Outer.Block0587
import Analysis.ContourCertificates.Outer.Block0588
import Analysis.ContourCertificates.Outer.Block0589
import Analysis.ContourCertificates.Outer.Block0590
import Analysis.ContourCertificates.Outer.Block0591

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch073

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0584.cells ++
  DirichletL.ContourCertificates.Outer.Block0585.cells ++
  DirichletL.ContourCertificates.Outer.Block0586.cells ++
  DirichletL.ContourCertificates.Outer.Block0587.cells ++
  DirichletL.ContourCertificates.Outer.Block0588.cells ++
  DirichletL.ContourCertificates.Outer.Block0589.cells ++
  DirichletL.ContourCertificates.Outer.Block0590.cells ++
  DirichletL.ContourCertificates.Outer.Block0591.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0584.cells_bounded, DirichletL.ContourCertificates.Outer.Block0585.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0586.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0587.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0588.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0589.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0590.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0591.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch073
