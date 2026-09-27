import Analysis.ContourCertificates.Outer.Block1280
import Analysis.ContourCertificates.Outer.Block1281
import Analysis.ContourCertificates.Outer.Block1282
import Analysis.ContourCertificates.Outer.Block1283
import Analysis.ContourCertificates.Outer.Block1284
import Analysis.ContourCertificates.Outer.Block1285
import Analysis.ContourCertificates.Outer.Block1286
import Analysis.ContourCertificates.Outer.Block1287

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch160

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1280.cells ++
  DirichletL.ContourCertificates.Outer.Block1281.cells ++
  DirichletL.ContourCertificates.Outer.Block1282.cells ++
  DirichletL.ContourCertificates.Outer.Block1283.cells ++
  DirichletL.ContourCertificates.Outer.Block1284.cells ++
  DirichletL.ContourCertificates.Outer.Block1285.cells ++
  DirichletL.ContourCertificates.Outer.Block1286.cells ++
  DirichletL.ContourCertificates.Outer.Block1287.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1280.cells_bounded, DirichletL.ContourCertificates.Outer.Block1281.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1282.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1283.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1284.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1285.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1286.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1287.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch160
