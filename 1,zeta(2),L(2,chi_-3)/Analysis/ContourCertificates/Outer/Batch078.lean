import Analysis.ContourCertificates.Outer.Block0624
import Analysis.ContourCertificates.Outer.Block0625
import Analysis.ContourCertificates.Outer.Block0626
import Analysis.ContourCertificates.Outer.Block0627
import Analysis.ContourCertificates.Outer.Block0628
import Analysis.ContourCertificates.Outer.Block0629
import Analysis.ContourCertificates.Outer.Block0630
import Analysis.ContourCertificates.Outer.Block0631

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch078

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0624.cells ++
  DirichletL.ContourCertificates.Outer.Block0625.cells ++
  DirichletL.ContourCertificates.Outer.Block0626.cells ++
  DirichletL.ContourCertificates.Outer.Block0627.cells ++
  DirichletL.ContourCertificates.Outer.Block0628.cells ++
  DirichletL.ContourCertificates.Outer.Block0629.cells ++
  DirichletL.ContourCertificates.Outer.Block0630.cells ++
  DirichletL.ContourCertificates.Outer.Block0631.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0624.cells_bounded, DirichletL.ContourCertificates.Outer.Block0625.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0626.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0627.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0628.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0629.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0630.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0631.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch078
