import Analysis.ContourCertificates.Outer.Block0168
import Analysis.ContourCertificates.Outer.Block0169
import Analysis.ContourCertificates.Outer.Block0170
import Analysis.ContourCertificates.Outer.Block0171
import Analysis.ContourCertificates.Outer.Block0172
import Analysis.ContourCertificates.Outer.Block0173
import Analysis.ContourCertificates.Outer.Block0174
import Analysis.ContourCertificates.Outer.Block0175

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch021

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0168.cells ++
  DirichletL.ContourCertificates.Outer.Block0169.cells ++
  DirichletL.ContourCertificates.Outer.Block0170.cells ++
  DirichletL.ContourCertificates.Outer.Block0171.cells ++
  DirichletL.ContourCertificates.Outer.Block0172.cells ++
  DirichletL.ContourCertificates.Outer.Block0173.cells ++
  DirichletL.ContourCertificates.Outer.Block0174.cells ++
  DirichletL.ContourCertificates.Outer.Block0175.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0168.cells_bounded, DirichletL.ContourCertificates.Outer.Block0169.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0170.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0171.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0172.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0173.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0174.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0175.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch021
