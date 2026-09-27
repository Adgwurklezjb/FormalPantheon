import Analysis.ContourCertificates.Inner.Block0160
import Analysis.ContourCertificates.Inner.Block0161
import Analysis.ContourCertificates.Inner.Block0162
import Analysis.ContourCertificates.Inner.Block0163
import Analysis.ContourCertificates.Inner.Block0164
import Analysis.ContourCertificates.Inner.Block0165
import Analysis.ContourCertificates.Inner.Block0166
import Analysis.ContourCertificates.Inner.Block0167

/-!
Consecutive inner cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Inner.Batch020

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Inner.Block0160.cells ++
  DirichletL.ContourCertificates.Inner.Block0161.cells ++
  DirichletL.ContourCertificates.Inner.Block0162.cells ++
  DirichletL.ContourCertificates.Inner.Block0163.cells ++
  DirichletL.ContourCertificates.Inner.Block0164.cells ++
  DirichletL.ContourCertificates.Inner.Block0165.cells ++
  DirichletL.ContourCertificates.Inner.Block0166.cells ++
  DirichletL.ContourCertificates.Inner.Block0167.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 true cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Inner.Block0160.cells_bounded, DirichletL.ContourCertificates.Inner.Block0161.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0162.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0163.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0164.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0165.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0166.cells_bounded⟩, DirichletL.ContourCertificates.Inner.Block0167.cells_bounded⟩

end DirichletL.ContourCertificates.Inner.Batch020
