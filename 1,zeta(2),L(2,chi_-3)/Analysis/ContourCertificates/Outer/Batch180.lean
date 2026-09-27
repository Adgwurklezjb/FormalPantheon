import Analysis.ContourCertificates.Outer.Block1440
import Analysis.ContourCertificates.Outer.Block1441
import Analysis.ContourCertificates.Outer.Block1442
import Analysis.ContourCertificates.Outer.Block1443
import Analysis.ContourCertificates.Outer.Block1444
import Analysis.ContourCertificates.Outer.Block1445
import Analysis.ContourCertificates.Outer.Block1446
import Analysis.ContourCertificates.Outer.Block1447

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch180

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1440.cells ++
  DirichletL.ContourCertificates.Outer.Block1441.cells ++
  DirichletL.ContourCertificates.Outer.Block1442.cells ++
  DirichletL.ContourCertificates.Outer.Block1443.cells ++
  DirichletL.ContourCertificates.Outer.Block1444.cells ++
  DirichletL.ContourCertificates.Outer.Block1445.cells ++
  DirichletL.ContourCertificates.Outer.Block1446.cells ++
  DirichletL.ContourCertificates.Outer.Block1447.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1440.cells_bounded, DirichletL.ContourCertificates.Outer.Block1441.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1442.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1443.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1444.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1445.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1446.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1447.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch180
