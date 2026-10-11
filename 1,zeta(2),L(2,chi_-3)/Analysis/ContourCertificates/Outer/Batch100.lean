import Analysis.ContourCertificates.Outer.Block0800
import Analysis.ContourCertificates.Outer.Block0801
import Analysis.ContourCertificates.Outer.Block0802
import Analysis.ContourCertificates.Outer.Block0803
import Analysis.ContourCertificates.Outer.Block0804
import Analysis.ContourCertificates.Outer.Block0805
import Analysis.ContourCertificates.Outer.Block0806
import Analysis.ContourCertificates.Outer.Block0807

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch100

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0800.cells ++
  DirichletL.ContourCertificates.Outer.Block0801.cells ++
  DirichletL.ContourCertificates.Outer.Block0802.cells ++
  DirichletL.ContourCertificates.Outer.Block0803.cells ++
  DirichletL.ContourCertificates.Outer.Block0804.cells ++
  DirichletL.ContourCertificates.Outer.Block0805.cells ++
  DirichletL.ContourCertificates.Outer.Block0806.cells ++
  DirichletL.ContourCertificates.Outer.Block0807.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0800.cells_bounded, DirichletL.ContourCertificates.Outer.Block0801.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0802.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0803.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0804.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0805.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0806.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0807.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch100
