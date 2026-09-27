import Analysis.ContourCertificates.Outer.Block0536
import Analysis.ContourCertificates.Outer.Block0537
import Analysis.ContourCertificates.Outer.Block0538
import Analysis.ContourCertificates.Outer.Block0539
import Analysis.ContourCertificates.Outer.Block0540
import Analysis.ContourCertificates.Outer.Block0541
import Analysis.ContourCertificates.Outer.Block0542
import Analysis.ContourCertificates.Outer.Block0543

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch067

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0536.cells ++
  DirichletL.ContourCertificates.Outer.Block0537.cells ++
  DirichletL.ContourCertificates.Outer.Block0538.cells ++
  DirichletL.ContourCertificates.Outer.Block0539.cells ++
  DirichletL.ContourCertificates.Outer.Block0540.cells ++
  DirichletL.ContourCertificates.Outer.Block0541.cells ++
  DirichletL.ContourCertificates.Outer.Block0542.cells ++
  DirichletL.ContourCertificates.Outer.Block0543.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0536.cells_bounded, DirichletL.ContourCertificates.Outer.Block0537.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0538.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0539.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0540.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0541.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0542.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0543.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch067
