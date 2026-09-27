import Analysis.ContourCertificates.Outer.Block1272
import Analysis.ContourCertificates.Outer.Block1273
import Analysis.ContourCertificates.Outer.Block1274
import Analysis.ContourCertificates.Outer.Block1275
import Analysis.ContourCertificates.Outer.Block1276
import Analysis.ContourCertificates.Outer.Block1277
import Analysis.ContourCertificates.Outer.Block1278
import Analysis.ContourCertificates.Outer.Block1279

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch159

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1272.cells ++
  DirichletL.ContourCertificates.Outer.Block1273.cells ++
  DirichletL.ContourCertificates.Outer.Block1274.cells ++
  DirichletL.ContourCertificates.Outer.Block1275.cells ++
  DirichletL.ContourCertificates.Outer.Block1276.cells ++
  DirichletL.ContourCertificates.Outer.Block1277.cells ++
  DirichletL.ContourCertificates.Outer.Block1278.cells ++
  DirichletL.ContourCertificates.Outer.Block1279.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1272.cells_bounded, DirichletL.ContourCertificates.Outer.Block1273.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1274.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1275.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1276.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1277.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1278.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1279.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch159
