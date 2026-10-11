import Analysis.ContourCertificates.Outer.Block0528
import Analysis.ContourCertificates.Outer.Block0529
import Analysis.ContourCertificates.Outer.Block0530
import Analysis.ContourCertificates.Outer.Block0531
import Analysis.ContourCertificates.Outer.Block0532
import Analysis.ContourCertificates.Outer.Block0533
import Analysis.ContourCertificates.Outer.Block0534
import Analysis.ContourCertificates.Outer.Block0535

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch066

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0528.cells ++
  DirichletL.ContourCertificates.Outer.Block0529.cells ++
  DirichletL.ContourCertificates.Outer.Block0530.cells ++
  DirichletL.ContourCertificates.Outer.Block0531.cells ++
  DirichletL.ContourCertificates.Outer.Block0532.cells ++
  DirichletL.ContourCertificates.Outer.Block0533.cells ++
  DirichletL.ContourCertificates.Outer.Block0534.cells ++
  DirichletL.ContourCertificates.Outer.Block0535.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0528.cells_bounded, DirichletL.ContourCertificates.Outer.Block0529.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0530.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0531.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0532.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0533.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0534.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0535.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch066
