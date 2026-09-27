import Analysis.ContourCertificates.Outer.Block0752
import Analysis.ContourCertificates.Outer.Block0753
import Analysis.ContourCertificates.Outer.Block0754
import Analysis.ContourCertificates.Outer.Block0755
import Analysis.ContourCertificates.Outer.Block0756
import Analysis.ContourCertificates.Outer.Block0757
import Analysis.ContourCertificates.Outer.Block0758
import Analysis.ContourCertificates.Outer.Block0759

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch094

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0752.cells ++
  DirichletL.ContourCertificates.Outer.Block0753.cells ++
  DirichletL.ContourCertificates.Outer.Block0754.cells ++
  DirichletL.ContourCertificates.Outer.Block0755.cells ++
  DirichletL.ContourCertificates.Outer.Block0756.cells ++
  DirichletL.ContourCertificates.Outer.Block0757.cells ++
  DirichletL.ContourCertificates.Outer.Block0758.cells ++
  DirichletL.ContourCertificates.Outer.Block0759.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0752.cells_bounded, DirichletL.ContourCertificates.Outer.Block0753.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0754.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0755.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0756.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0757.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0758.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0759.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch094
