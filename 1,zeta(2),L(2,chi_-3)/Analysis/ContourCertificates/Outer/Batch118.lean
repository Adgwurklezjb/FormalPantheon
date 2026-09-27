import Analysis.ContourCertificates.Outer.Block0944
import Analysis.ContourCertificates.Outer.Block0945
import Analysis.ContourCertificates.Outer.Block0946
import Analysis.ContourCertificates.Outer.Block0947
import Analysis.ContourCertificates.Outer.Block0948
import Analysis.ContourCertificates.Outer.Block0949
import Analysis.ContourCertificates.Outer.Block0950
import Analysis.ContourCertificates.Outer.Block0951

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch118

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0944.cells ++
  DirichletL.ContourCertificates.Outer.Block0945.cells ++
  DirichletL.ContourCertificates.Outer.Block0946.cells ++
  DirichletL.ContourCertificates.Outer.Block0947.cells ++
  DirichletL.ContourCertificates.Outer.Block0948.cells ++
  DirichletL.ContourCertificates.Outer.Block0949.cells ++
  DirichletL.ContourCertificates.Outer.Block0950.cells ++
  DirichletL.ContourCertificates.Outer.Block0951.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0944.cells_bounded, DirichletL.ContourCertificates.Outer.Block0945.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0946.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0947.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0948.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0949.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0950.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0951.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch118
