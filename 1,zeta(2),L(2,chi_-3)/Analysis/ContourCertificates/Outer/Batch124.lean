import Analysis.ContourCertificates.Outer.Block0992
import Analysis.ContourCertificates.Outer.Block0993
import Analysis.ContourCertificates.Outer.Block0994
import Analysis.ContourCertificates.Outer.Block0995
import Analysis.ContourCertificates.Outer.Block0996
import Analysis.ContourCertificates.Outer.Block0997
import Analysis.ContourCertificates.Outer.Block0998
import Analysis.ContourCertificates.Outer.Block0999

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch124

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0992.cells ++
  DirichletL.ContourCertificates.Outer.Block0993.cells ++
  DirichletL.ContourCertificates.Outer.Block0994.cells ++
  DirichletL.ContourCertificates.Outer.Block0995.cells ++
  DirichletL.ContourCertificates.Outer.Block0996.cells ++
  DirichletL.ContourCertificates.Outer.Block0997.cells ++
  DirichletL.ContourCertificates.Outer.Block0998.cells ++
  DirichletL.ContourCertificates.Outer.Block0999.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0992.cells_bounded, DirichletL.ContourCertificates.Outer.Block0993.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0994.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0995.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0996.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0997.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0998.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0999.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch124
