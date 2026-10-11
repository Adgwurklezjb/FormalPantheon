import Analysis.ContourCertificates.Outer.Block0608
import Analysis.ContourCertificates.Outer.Block0609
import Analysis.ContourCertificates.Outer.Block0610
import Analysis.ContourCertificates.Outer.Block0611
import Analysis.ContourCertificates.Outer.Block0612
import Analysis.ContourCertificates.Outer.Block0613
import Analysis.ContourCertificates.Outer.Block0614
import Analysis.ContourCertificates.Outer.Block0615

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch076

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0608.cells ++
  DirichletL.ContourCertificates.Outer.Block0609.cells ++
  DirichletL.ContourCertificates.Outer.Block0610.cells ++
  DirichletL.ContourCertificates.Outer.Block0611.cells ++
  DirichletL.ContourCertificates.Outer.Block0612.cells ++
  DirichletL.ContourCertificates.Outer.Block0613.cells ++
  DirichletL.ContourCertificates.Outer.Block0614.cells ++
  DirichletL.ContourCertificates.Outer.Block0615.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0608.cells_bounded, DirichletL.ContourCertificates.Outer.Block0609.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0610.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0611.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0612.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0613.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0614.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0615.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch076
