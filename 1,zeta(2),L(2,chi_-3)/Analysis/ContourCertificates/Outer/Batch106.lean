import Analysis.ContourCertificates.Outer.Block0848
import Analysis.ContourCertificates.Outer.Block0849
import Analysis.ContourCertificates.Outer.Block0850
import Analysis.ContourCertificates.Outer.Block0851
import Analysis.ContourCertificates.Outer.Block0852
import Analysis.ContourCertificates.Outer.Block0853
import Analysis.ContourCertificates.Outer.Block0854
import Analysis.ContourCertificates.Outer.Block0855

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch106

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0848.cells ++
  DirichletL.ContourCertificates.Outer.Block0849.cells ++
  DirichletL.ContourCertificates.Outer.Block0850.cells ++
  DirichletL.ContourCertificates.Outer.Block0851.cells ++
  DirichletL.ContourCertificates.Outer.Block0852.cells ++
  DirichletL.ContourCertificates.Outer.Block0853.cells ++
  DirichletL.ContourCertificates.Outer.Block0854.cells ++
  DirichletL.ContourCertificates.Outer.Block0855.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0848.cells_bounded, DirichletL.ContourCertificates.Outer.Block0849.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0850.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0851.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0852.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0853.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0854.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0855.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch106
