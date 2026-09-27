import Analysis.ContourCertificates.Outer.Block0928
import Analysis.ContourCertificates.Outer.Block0929
import Analysis.ContourCertificates.Outer.Block0930
import Analysis.ContourCertificates.Outer.Block0931
import Analysis.ContourCertificates.Outer.Block0932
import Analysis.ContourCertificates.Outer.Block0933
import Analysis.ContourCertificates.Outer.Block0934
import Analysis.ContourCertificates.Outer.Block0935

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch116

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0928.cells ++
  DirichletL.ContourCertificates.Outer.Block0929.cells ++
  DirichletL.ContourCertificates.Outer.Block0930.cells ++
  DirichletL.ContourCertificates.Outer.Block0931.cells ++
  DirichletL.ContourCertificates.Outer.Block0932.cells ++
  DirichletL.ContourCertificates.Outer.Block0933.cells ++
  DirichletL.ContourCertificates.Outer.Block0934.cells ++
  DirichletL.ContourCertificates.Outer.Block0935.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0928.cells_bounded, DirichletL.ContourCertificates.Outer.Block0929.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0930.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0931.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0932.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0933.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0934.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0935.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch116
