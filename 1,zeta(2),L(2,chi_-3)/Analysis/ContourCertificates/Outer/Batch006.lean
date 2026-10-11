import Analysis.ContourCertificates.Outer.Block0048
import Analysis.ContourCertificates.Outer.Block0049
import Analysis.ContourCertificates.Outer.Block0050
import Analysis.ContourCertificates.Outer.Block0051
import Analysis.ContourCertificates.Outer.Block0052
import Analysis.ContourCertificates.Outer.Block0053
import Analysis.ContourCertificates.Outer.Block0054
import Analysis.ContourCertificates.Outer.Block0055

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch006

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0048.cells ++
  DirichletL.ContourCertificates.Outer.Block0049.cells ++
  DirichletL.ContourCertificates.Outer.Block0050.cells ++
  DirichletL.ContourCertificates.Outer.Block0051.cells ++
  DirichletL.ContourCertificates.Outer.Block0052.cells ++
  DirichletL.ContourCertificates.Outer.Block0053.cells ++
  DirichletL.ContourCertificates.Outer.Block0054.cells ++
  DirichletL.ContourCertificates.Outer.Block0055.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0048.cells_bounded, DirichletL.ContourCertificates.Outer.Block0049.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0050.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0051.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0052.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0053.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0054.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0055.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch006
