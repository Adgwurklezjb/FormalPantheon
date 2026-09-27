import Analysis.ContourCertificates.Outer.Block0216
import Analysis.ContourCertificates.Outer.Block0217
import Analysis.ContourCertificates.Outer.Block0218
import Analysis.ContourCertificates.Outer.Block0219
import Analysis.ContourCertificates.Outer.Block0220
import Analysis.ContourCertificates.Outer.Block0221
import Analysis.ContourCertificates.Outer.Block0222
import Analysis.ContourCertificates.Outer.Block0223

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch027

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0216.cells ++
  DirichletL.ContourCertificates.Outer.Block0217.cells ++
  DirichletL.ContourCertificates.Outer.Block0218.cells ++
  DirichletL.ContourCertificates.Outer.Block0219.cells ++
  DirichletL.ContourCertificates.Outer.Block0220.cells ++
  DirichletL.ContourCertificates.Outer.Block0221.cells ++
  DirichletL.ContourCertificates.Outer.Block0222.cells ++
  DirichletL.ContourCertificates.Outer.Block0223.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0216.cells_bounded, DirichletL.ContourCertificates.Outer.Block0217.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0218.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0219.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0220.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0221.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0222.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0223.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch027
