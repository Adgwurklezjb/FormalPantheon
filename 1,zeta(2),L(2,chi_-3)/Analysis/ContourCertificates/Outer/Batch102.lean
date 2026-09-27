import Analysis.ContourCertificates.Outer.Block0816
import Analysis.ContourCertificates.Outer.Block0817
import Analysis.ContourCertificates.Outer.Block0818
import Analysis.ContourCertificates.Outer.Block0819
import Analysis.ContourCertificates.Outer.Block0820
import Analysis.ContourCertificates.Outer.Block0821
import Analysis.ContourCertificates.Outer.Block0822
import Analysis.ContourCertificates.Outer.Block0823

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch102

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0816.cells ++
  DirichletL.ContourCertificates.Outer.Block0817.cells ++
  DirichletL.ContourCertificates.Outer.Block0818.cells ++
  DirichletL.ContourCertificates.Outer.Block0819.cells ++
  DirichletL.ContourCertificates.Outer.Block0820.cells ++
  DirichletL.ContourCertificates.Outer.Block0821.cells ++
  DirichletL.ContourCertificates.Outer.Block0822.cells ++
  DirichletL.ContourCertificates.Outer.Block0823.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0816.cells_bounded, DirichletL.ContourCertificates.Outer.Block0817.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0818.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0819.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0820.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0821.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0822.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0823.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch102
