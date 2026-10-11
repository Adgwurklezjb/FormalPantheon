import Analysis.ContourCertificates.Outer.Block0912
import Analysis.ContourCertificates.Outer.Block0913
import Analysis.ContourCertificates.Outer.Block0914
import Analysis.ContourCertificates.Outer.Block0915
import Analysis.ContourCertificates.Outer.Block0916
import Analysis.ContourCertificates.Outer.Block0917
import Analysis.ContourCertificates.Outer.Block0918
import Analysis.ContourCertificates.Outer.Block0919

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch114

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0912.cells ++
  DirichletL.ContourCertificates.Outer.Block0913.cells ++
  DirichletL.ContourCertificates.Outer.Block0914.cells ++
  DirichletL.ContourCertificates.Outer.Block0915.cells ++
  DirichletL.ContourCertificates.Outer.Block0916.cells ++
  DirichletL.ContourCertificates.Outer.Block0917.cells ++
  DirichletL.ContourCertificates.Outer.Block0918.cells ++
  DirichletL.ContourCertificates.Outer.Block0919.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0912.cells_bounded, DirichletL.ContourCertificates.Outer.Block0913.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0914.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0915.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0916.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0917.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0918.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0919.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch114
