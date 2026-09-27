import Analysis.ContourCertificates.Outer.Block0960
import Analysis.ContourCertificates.Outer.Block0961
import Analysis.ContourCertificates.Outer.Block0962
import Analysis.ContourCertificates.Outer.Block0963
import Analysis.ContourCertificates.Outer.Block0964
import Analysis.ContourCertificates.Outer.Block0965
import Analysis.ContourCertificates.Outer.Block0966
import Analysis.ContourCertificates.Outer.Block0967

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch120

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0960.cells ++
  DirichletL.ContourCertificates.Outer.Block0961.cells ++
  DirichletL.ContourCertificates.Outer.Block0962.cells ++
  DirichletL.ContourCertificates.Outer.Block0963.cells ++
  DirichletL.ContourCertificates.Outer.Block0964.cells ++
  DirichletL.ContourCertificates.Outer.Block0965.cells ++
  DirichletL.ContourCertificates.Outer.Block0966.cells ++
  DirichletL.ContourCertificates.Outer.Block0967.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0960.cells_bounded, DirichletL.ContourCertificates.Outer.Block0961.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0962.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0963.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0964.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0965.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0966.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0967.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch120
