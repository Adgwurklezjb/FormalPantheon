import Analysis.ContourCertificates.Outer.Block0568
import Analysis.ContourCertificates.Outer.Block0569
import Analysis.ContourCertificates.Outer.Block0570
import Analysis.ContourCertificates.Outer.Block0571
import Analysis.ContourCertificates.Outer.Block0572
import Analysis.ContourCertificates.Outer.Block0573
import Analysis.ContourCertificates.Outer.Block0574
import Analysis.ContourCertificates.Outer.Block0575

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch071

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0568.cells ++
  DirichletL.ContourCertificates.Outer.Block0569.cells ++
  DirichletL.ContourCertificates.Outer.Block0570.cells ++
  DirichletL.ContourCertificates.Outer.Block0571.cells ++
  DirichletL.ContourCertificates.Outer.Block0572.cells ++
  DirichletL.ContourCertificates.Outer.Block0573.cells ++
  DirichletL.ContourCertificates.Outer.Block0574.cells ++
  DirichletL.ContourCertificates.Outer.Block0575.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0568.cells_bounded, DirichletL.ContourCertificates.Outer.Block0569.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0570.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0571.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0572.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0573.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0574.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0575.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch071
