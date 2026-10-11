import Analysis.ContourCertificates.Outer.Block0360
import Analysis.ContourCertificates.Outer.Block0361
import Analysis.ContourCertificates.Outer.Block0362
import Analysis.ContourCertificates.Outer.Block0363
import Analysis.ContourCertificates.Outer.Block0364
import Analysis.ContourCertificates.Outer.Block0365
import Analysis.ContourCertificates.Outer.Block0366
import Analysis.ContourCertificates.Outer.Block0367

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch045

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0360.cells ++
  DirichletL.ContourCertificates.Outer.Block0361.cells ++
  DirichletL.ContourCertificates.Outer.Block0362.cells ++
  DirichletL.ContourCertificates.Outer.Block0363.cells ++
  DirichletL.ContourCertificates.Outer.Block0364.cells ++
  DirichletL.ContourCertificates.Outer.Block0365.cells ++
  DirichletL.ContourCertificates.Outer.Block0366.cells ++
  DirichletL.ContourCertificates.Outer.Block0367.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0360.cells_bounded, DirichletL.ContourCertificates.Outer.Block0361.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0362.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0363.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0364.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0365.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0366.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0367.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch045
