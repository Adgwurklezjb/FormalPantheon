import Analysis.ContourCertificates.Outer.Block0904
import Analysis.ContourCertificates.Outer.Block0905
import Analysis.ContourCertificates.Outer.Block0906
import Analysis.ContourCertificates.Outer.Block0907
import Analysis.ContourCertificates.Outer.Block0908
import Analysis.ContourCertificates.Outer.Block0909
import Analysis.ContourCertificates.Outer.Block0910
import Analysis.ContourCertificates.Outer.Block0911

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch113

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0904.cells ++
  DirichletL.ContourCertificates.Outer.Block0905.cells ++
  DirichletL.ContourCertificates.Outer.Block0906.cells ++
  DirichletL.ContourCertificates.Outer.Block0907.cells ++
  DirichletL.ContourCertificates.Outer.Block0908.cells ++
  DirichletL.ContourCertificates.Outer.Block0909.cells ++
  DirichletL.ContourCertificates.Outer.Block0910.cells ++
  DirichletL.ContourCertificates.Outer.Block0911.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0904.cells_bounded, DirichletL.ContourCertificates.Outer.Block0905.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0906.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0907.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0908.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0909.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0910.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0911.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch113
