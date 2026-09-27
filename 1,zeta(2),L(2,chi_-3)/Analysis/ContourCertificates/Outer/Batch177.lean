import Analysis.ContourCertificates.Outer.Block1416
import Analysis.ContourCertificates.Outer.Block1417
import Analysis.ContourCertificates.Outer.Block1418
import Analysis.ContourCertificates.Outer.Block1419
import Analysis.ContourCertificates.Outer.Block1420
import Analysis.ContourCertificates.Outer.Block1421
import Analysis.ContourCertificates.Outer.Block1422
import Analysis.ContourCertificates.Outer.Block1423

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch177

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1416.cells ++
  DirichletL.ContourCertificates.Outer.Block1417.cells ++
  DirichletL.ContourCertificates.Outer.Block1418.cells ++
  DirichletL.ContourCertificates.Outer.Block1419.cells ++
  DirichletL.ContourCertificates.Outer.Block1420.cells ++
  DirichletL.ContourCertificates.Outer.Block1421.cells ++
  DirichletL.ContourCertificates.Outer.Block1422.cells ++
  DirichletL.ContourCertificates.Outer.Block1423.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1416.cells_bounded, DirichletL.ContourCertificates.Outer.Block1417.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1418.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1419.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1420.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1421.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1422.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1423.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch177
