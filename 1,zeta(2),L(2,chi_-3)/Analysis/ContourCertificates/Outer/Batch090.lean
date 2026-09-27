import Analysis.ContourCertificates.Outer.Block0720
import Analysis.ContourCertificates.Outer.Block0721
import Analysis.ContourCertificates.Outer.Block0722
import Analysis.ContourCertificates.Outer.Block0723
import Analysis.ContourCertificates.Outer.Block0724
import Analysis.ContourCertificates.Outer.Block0725
import Analysis.ContourCertificates.Outer.Block0726
import Analysis.ContourCertificates.Outer.Block0727

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch090

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0720.cells ++
  DirichletL.ContourCertificates.Outer.Block0721.cells ++
  DirichletL.ContourCertificates.Outer.Block0722.cells ++
  DirichletL.ContourCertificates.Outer.Block0723.cells ++
  DirichletL.ContourCertificates.Outer.Block0724.cells ++
  DirichletL.ContourCertificates.Outer.Block0725.cells ++
  DirichletL.ContourCertificates.Outer.Block0726.cells ++
  DirichletL.ContourCertificates.Outer.Block0727.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0720.cells_bounded, DirichletL.ContourCertificates.Outer.Block0721.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0722.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0723.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0724.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0725.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0726.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0727.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch090
