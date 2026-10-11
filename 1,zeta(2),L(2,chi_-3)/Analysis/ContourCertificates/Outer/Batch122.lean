import Analysis.ContourCertificates.Outer.Block0976
import Analysis.ContourCertificates.Outer.Block0977
import Analysis.ContourCertificates.Outer.Block0978
import Analysis.ContourCertificates.Outer.Block0979
import Analysis.ContourCertificates.Outer.Block0980
import Analysis.ContourCertificates.Outer.Block0981
import Analysis.ContourCertificates.Outer.Block0982
import Analysis.ContourCertificates.Outer.Block0983

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch122

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0976.cells ++
  DirichletL.ContourCertificates.Outer.Block0977.cells ++
  DirichletL.ContourCertificates.Outer.Block0978.cells ++
  DirichletL.ContourCertificates.Outer.Block0979.cells ++
  DirichletL.ContourCertificates.Outer.Block0980.cells ++
  DirichletL.ContourCertificates.Outer.Block0981.cells ++
  DirichletL.ContourCertificates.Outer.Block0982.cells ++
  DirichletL.ContourCertificates.Outer.Block0983.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0976.cells_bounded, DirichletL.ContourCertificates.Outer.Block0977.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0978.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0979.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0980.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0981.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0982.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0983.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch122
