import Analysis.ContourCertificates.Outer.Block0864
import Analysis.ContourCertificates.Outer.Block0865
import Analysis.ContourCertificates.Outer.Block0866
import Analysis.ContourCertificates.Outer.Block0867
import Analysis.ContourCertificates.Outer.Block0868
import Analysis.ContourCertificates.Outer.Block0869
import Analysis.ContourCertificates.Outer.Block0870
import Analysis.ContourCertificates.Outer.Block0871

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch108

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0864.cells ++
  DirichletL.ContourCertificates.Outer.Block0865.cells ++
  DirichletL.ContourCertificates.Outer.Block0866.cells ++
  DirichletL.ContourCertificates.Outer.Block0867.cells ++
  DirichletL.ContourCertificates.Outer.Block0868.cells ++
  DirichletL.ContourCertificates.Outer.Block0869.cells ++
  DirichletL.ContourCertificates.Outer.Block0870.cells ++
  DirichletL.ContourCertificates.Outer.Block0871.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0864.cells_bounded, DirichletL.ContourCertificates.Outer.Block0865.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0866.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0867.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0868.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0869.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0870.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0871.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch108
