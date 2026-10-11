import Analysis.ContourCertificates.Outer.Block0688
import Analysis.ContourCertificates.Outer.Block0689
import Analysis.ContourCertificates.Outer.Block0690
import Analysis.ContourCertificates.Outer.Block0691
import Analysis.ContourCertificates.Outer.Block0692
import Analysis.ContourCertificates.Outer.Block0693
import Analysis.ContourCertificates.Outer.Block0694
import Analysis.ContourCertificates.Outer.Block0695

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch086

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0688.cells ++
  DirichletL.ContourCertificates.Outer.Block0689.cells ++
  DirichletL.ContourCertificates.Outer.Block0690.cells ++
  DirichletL.ContourCertificates.Outer.Block0691.cells ++
  DirichletL.ContourCertificates.Outer.Block0692.cells ++
  DirichletL.ContourCertificates.Outer.Block0693.cells ++
  DirichletL.ContourCertificates.Outer.Block0694.cells ++
  DirichletL.ContourCertificates.Outer.Block0695.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0688.cells_bounded, DirichletL.ContourCertificates.Outer.Block0689.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0690.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0691.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0692.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0693.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0694.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0695.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch086
