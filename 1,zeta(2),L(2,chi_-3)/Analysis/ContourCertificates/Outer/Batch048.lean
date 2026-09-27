import Analysis.ContourCertificates.Outer.Block0384
import Analysis.ContourCertificates.Outer.Block0385
import Analysis.ContourCertificates.Outer.Block0386
import Analysis.ContourCertificates.Outer.Block0387
import Analysis.ContourCertificates.Outer.Block0388
import Analysis.ContourCertificates.Outer.Block0389
import Analysis.ContourCertificates.Outer.Block0390
import Analysis.ContourCertificates.Outer.Block0391

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch048

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0384.cells ++
  DirichletL.ContourCertificates.Outer.Block0385.cells ++
  DirichletL.ContourCertificates.Outer.Block0386.cells ++
  DirichletL.ContourCertificates.Outer.Block0387.cells ++
  DirichletL.ContourCertificates.Outer.Block0388.cells ++
  DirichletL.ContourCertificates.Outer.Block0389.cells ++
  DirichletL.ContourCertificates.Outer.Block0390.cells ++
  DirichletL.ContourCertificates.Outer.Block0391.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0384.cells_bounded, DirichletL.ContourCertificates.Outer.Block0385.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0386.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0387.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0388.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0389.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0390.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0391.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch048
