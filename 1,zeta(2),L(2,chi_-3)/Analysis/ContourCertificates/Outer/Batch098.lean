import Analysis.ContourCertificates.Outer.Block0784
import Analysis.ContourCertificates.Outer.Block0785
import Analysis.ContourCertificates.Outer.Block0786
import Analysis.ContourCertificates.Outer.Block0787
import Analysis.ContourCertificates.Outer.Block0788
import Analysis.ContourCertificates.Outer.Block0789
import Analysis.ContourCertificates.Outer.Block0790
import Analysis.ContourCertificates.Outer.Block0791

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch098

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0784.cells ++
  DirichletL.ContourCertificates.Outer.Block0785.cells ++
  DirichletL.ContourCertificates.Outer.Block0786.cells ++
  DirichletL.ContourCertificates.Outer.Block0787.cells ++
  DirichletL.ContourCertificates.Outer.Block0788.cells ++
  DirichletL.ContourCertificates.Outer.Block0789.cells ++
  DirichletL.ContourCertificates.Outer.Block0790.cells ++
  DirichletL.ContourCertificates.Outer.Block0791.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0784.cells_bounded, DirichletL.ContourCertificates.Outer.Block0785.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0786.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0787.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0788.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0789.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0790.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0791.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch098
