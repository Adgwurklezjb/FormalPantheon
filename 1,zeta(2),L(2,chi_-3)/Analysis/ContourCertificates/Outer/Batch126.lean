import Analysis.ContourCertificates.Outer.Block1008
import Analysis.ContourCertificates.Outer.Block1009
import Analysis.ContourCertificates.Outer.Block1010
import Analysis.ContourCertificates.Outer.Block1011
import Analysis.ContourCertificates.Outer.Block1012
import Analysis.ContourCertificates.Outer.Block1013
import Analysis.ContourCertificates.Outer.Block1014
import Analysis.ContourCertificates.Outer.Block1015

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch126

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1008.cells ++
  DirichletL.ContourCertificates.Outer.Block1009.cells ++
  DirichletL.ContourCertificates.Outer.Block1010.cells ++
  DirichletL.ContourCertificates.Outer.Block1011.cells ++
  DirichletL.ContourCertificates.Outer.Block1012.cells ++
  DirichletL.ContourCertificates.Outer.Block1013.cells ++
  DirichletL.ContourCertificates.Outer.Block1014.cells ++
  DirichletL.ContourCertificates.Outer.Block1015.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1008.cells_bounded, DirichletL.ContourCertificates.Outer.Block1009.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1010.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1011.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1012.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1013.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1014.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1015.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch126
