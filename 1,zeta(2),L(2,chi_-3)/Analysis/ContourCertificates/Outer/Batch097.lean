import Analysis.ContourCertificates.Outer.Block0776
import Analysis.ContourCertificates.Outer.Block0777
import Analysis.ContourCertificates.Outer.Block0778
import Analysis.ContourCertificates.Outer.Block0779
import Analysis.ContourCertificates.Outer.Block0780
import Analysis.ContourCertificates.Outer.Block0781
import Analysis.ContourCertificates.Outer.Block0782
import Analysis.ContourCertificates.Outer.Block0783

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch097

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0776.cells ++
  DirichletL.ContourCertificates.Outer.Block0777.cells ++
  DirichletL.ContourCertificates.Outer.Block0778.cells ++
  DirichletL.ContourCertificates.Outer.Block0779.cells ++
  DirichletL.ContourCertificates.Outer.Block0780.cells ++
  DirichletL.ContourCertificates.Outer.Block0781.cells ++
  DirichletL.ContourCertificates.Outer.Block0782.cells ++
  DirichletL.ContourCertificates.Outer.Block0783.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0776.cells_bounded, DirichletL.ContourCertificates.Outer.Block0777.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0778.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0779.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0780.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0781.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0782.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0783.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch097
