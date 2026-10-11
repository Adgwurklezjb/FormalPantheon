import Analysis.ContourCertificates.Outer.Block0376
import Analysis.ContourCertificates.Outer.Block0377
import Analysis.ContourCertificates.Outer.Block0378
import Analysis.ContourCertificates.Outer.Block0379
import Analysis.ContourCertificates.Outer.Block0380
import Analysis.ContourCertificates.Outer.Block0381
import Analysis.ContourCertificates.Outer.Block0382
import Analysis.ContourCertificates.Outer.Block0383

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch047

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0376.cells ++
  DirichletL.ContourCertificates.Outer.Block0377.cells ++
  DirichletL.ContourCertificates.Outer.Block0378.cells ++
  DirichletL.ContourCertificates.Outer.Block0379.cells ++
  DirichletL.ContourCertificates.Outer.Block0380.cells ++
  DirichletL.ContourCertificates.Outer.Block0381.cells ++
  DirichletL.ContourCertificates.Outer.Block0382.cells ++
  DirichletL.ContourCertificates.Outer.Block0383.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0376.cells_bounded, DirichletL.ContourCertificates.Outer.Block0377.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0378.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0379.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0380.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0381.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0382.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0383.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch047
