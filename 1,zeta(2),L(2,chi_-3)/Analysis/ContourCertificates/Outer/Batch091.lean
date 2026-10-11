import Analysis.ContourCertificates.Outer.Block0728
import Analysis.ContourCertificates.Outer.Block0729
import Analysis.ContourCertificates.Outer.Block0730
import Analysis.ContourCertificates.Outer.Block0731
import Analysis.ContourCertificates.Outer.Block0732
import Analysis.ContourCertificates.Outer.Block0733
import Analysis.ContourCertificates.Outer.Block0734
import Analysis.ContourCertificates.Outer.Block0735

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch091

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0728.cells ++
  DirichletL.ContourCertificates.Outer.Block0729.cells ++
  DirichletL.ContourCertificates.Outer.Block0730.cells ++
  DirichletL.ContourCertificates.Outer.Block0731.cells ++
  DirichletL.ContourCertificates.Outer.Block0732.cells ++
  DirichletL.ContourCertificates.Outer.Block0733.cells ++
  DirichletL.ContourCertificates.Outer.Block0734.cells ++
  DirichletL.ContourCertificates.Outer.Block0735.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0728.cells_bounded, DirichletL.ContourCertificates.Outer.Block0729.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0730.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0731.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0732.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0733.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0734.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0735.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch091
