import Analysis.ContourCertificates.Outer.Block0552
import Analysis.ContourCertificates.Outer.Block0553
import Analysis.ContourCertificates.Outer.Block0554
import Analysis.ContourCertificates.Outer.Block0555
import Analysis.ContourCertificates.Outer.Block0556
import Analysis.ContourCertificates.Outer.Block0557
import Analysis.ContourCertificates.Outer.Block0558
import Analysis.ContourCertificates.Outer.Block0559

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch069

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0552.cells ++
  DirichletL.ContourCertificates.Outer.Block0553.cells ++
  DirichletL.ContourCertificates.Outer.Block0554.cells ++
  DirichletL.ContourCertificates.Outer.Block0555.cells ++
  DirichletL.ContourCertificates.Outer.Block0556.cells ++
  DirichletL.ContourCertificates.Outer.Block0557.cells ++
  DirichletL.ContourCertificates.Outer.Block0558.cells ++
  DirichletL.ContourCertificates.Outer.Block0559.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0552.cells_bounded, DirichletL.ContourCertificates.Outer.Block0553.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0554.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0555.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0556.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0557.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0558.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0559.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch069
