import Analysis.ContourCertificates.Outer.Block0592
import Analysis.ContourCertificates.Outer.Block0593
import Analysis.ContourCertificates.Outer.Block0594
import Analysis.ContourCertificates.Outer.Block0595
import Analysis.ContourCertificates.Outer.Block0596
import Analysis.ContourCertificates.Outer.Block0597
import Analysis.ContourCertificates.Outer.Block0598
import Analysis.ContourCertificates.Outer.Block0599

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch074

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0592.cells ++
  DirichletL.ContourCertificates.Outer.Block0593.cells ++
  DirichletL.ContourCertificates.Outer.Block0594.cells ++
  DirichletL.ContourCertificates.Outer.Block0595.cells ++
  DirichletL.ContourCertificates.Outer.Block0596.cells ++
  DirichletL.ContourCertificates.Outer.Block0597.cells ++
  DirichletL.ContourCertificates.Outer.Block0598.cells ++
  DirichletL.ContourCertificates.Outer.Block0599.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0592.cells_bounded, DirichletL.ContourCertificates.Outer.Block0593.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0594.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0595.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0596.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0597.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0598.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0599.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch074
