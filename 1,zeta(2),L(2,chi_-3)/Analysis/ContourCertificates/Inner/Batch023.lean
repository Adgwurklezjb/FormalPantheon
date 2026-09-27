import Analysis.ContourCertificates.Inner.Block0184
import Analysis.ContourCertificates.Inner.Block0185
import Analysis.ContourCertificates.Inner.Block0186
import Analysis.ContourCertificates.Inner.Block0187
import Analysis.ContourCertificates.Inner.Block0188
import Analysis.ContourCertificates.Inner.Block0189
import Analysis.ContourCertificates.Inner.Block0190
import Analysis.ContourCertificates.Inner.Block0191

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch023

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0184.cells ++
  DirichletL.ContourCertificates.Inner.Block0185.cells ++
  DirichletL.ContourCertificates.Inner.Block0186.cells ++
  DirichletL.ContourCertificates.Inner.Block0187.cells ++
  DirichletL.ContourCertificates.Inner.Block0188.cells ++
  DirichletL.ContourCertificates.Inner.Block0189.cells ++
  DirichletL.ContourCertificates.Inner.Block0190.cells ++
  DirichletL.ContourCertificates.Inner.Block0191.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0184.cells_bounded, DirichletL.ContourCertificates.Inner.Block0185.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0186.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0187.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0188.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0189.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0190.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0191.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch023
