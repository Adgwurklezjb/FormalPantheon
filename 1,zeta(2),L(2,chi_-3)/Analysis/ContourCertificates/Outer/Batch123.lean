import Analysis.ContourCertificates.Outer.Block0984
import Analysis.ContourCertificates.Outer.Block0985
import Analysis.ContourCertificates.Outer.Block0986
import Analysis.ContourCertificates.Outer.Block0987
import Analysis.ContourCertificates.Outer.Block0988
import Analysis.ContourCertificates.Outer.Block0989
import Analysis.ContourCertificates.Outer.Block0990
import Analysis.ContourCertificates.Outer.Block0991

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch123

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0984.cells ++
  DirichletL.ContourCertificates.Outer.Block0985.cells ++
  DirichletL.ContourCertificates.Outer.Block0986.cells ++
  DirichletL.ContourCertificates.Outer.Block0987.cells ++
  DirichletL.ContourCertificates.Outer.Block0988.cells ++
  DirichletL.ContourCertificates.Outer.Block0989.cells ++
  DirichletL.ContourCertificates.Outer.Block0990.cells ++
  DirichletL.ContourCertificates.Outer.Block0991.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0984.cells_bounded, DirichletL.ContourCertificates.Outer.Block0985.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0986.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0987.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0988.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0989.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0990.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0991.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch123
