import Analysis.ContourCertificates.Outer.Block0064
import Analysis.ContourCertificates.Outer.Block0065
import Analysis.ContourCertificates.Outer.Block0066
import Analysis.ContourCertificates.Outer.Block0067
import Analysis.ContourCertificates.Outer.Block0068
import Analysis.ContourCertificates.Outer.Block0069
import Analysis.ContourCertificates.Outer.Block0070
import Analysis.ContourCertificates.Outer.Block0071

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch008

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0064.cells ++
  DirichletL.ContourCertificates.Outer.Block0065.cells ++
  DirichletL.ContourCertificates.Outer.Block0066.cells ++
  DirichletL.ContourCertificates.Outer.Block0067.cells ++
  DirichletL.ContourCertificates.Outer.Block0068.cells ++
  DirichletL.ContourCertificates.Outer.Block0069.cells ++
  DirichletL.ContourCertificates.Outer.Block0070.cells ++
  DirichletL.ContourCertificates.Outer.Block0071.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0064.cells_bounded, DirichletL.ContourCertificates.Outer.Block0065.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0066.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0067.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0068.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0069.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0070.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0071.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch008
