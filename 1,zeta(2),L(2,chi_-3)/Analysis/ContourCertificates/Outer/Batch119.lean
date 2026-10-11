import Analysis.ContourCertificates.Outer.Block0952
import Analysis.ContourCertificates.Outer.Block0953
import Analysis.ContourCertificates.Outer.Block0954
import Analysis.ContourCertificates.Outer.Block0955
import Analysis.ContourCertificates.Outer.Block0956
import Analysis.ContourCertificates.Outer.Block0957
import Analysis.ContourCertificates.Outer.Block0958
import Analysis.ContourCertificates.Outer.Block0959

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch119

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0952.cells ++
  DirichletL.ContourCertificates.Outer.Block0953.cells ++
  DirichletL.ContourCertificates.Outer.Block0954.cells ++
  DirichletL.ContourCertificates.Outer.Block0955.cells ++
  DirichletL.ContourCertificates.Outer.Block0956.cells ++
  DirichletL.ContourCertificates.Outer.Block0957.cells ++
  DirichletL.ContourCertificates.Outer.Block0958.cells ++
  DirichletL.ContourCertificates.Outer.Block0959.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0952.cells_bounded, DirichletL.ContourCertificates.Outer.Block0953.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0954.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0955.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0956.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0957.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0958.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0959.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch119
