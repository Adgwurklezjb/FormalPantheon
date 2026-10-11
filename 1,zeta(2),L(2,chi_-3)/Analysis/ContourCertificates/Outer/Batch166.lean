import Analysis.ContourCertificates.Outer.Block1328
import Analysis.ContourCertificates.Outer.Block1329
import Analysis.ContourCertificates.Outer.Block1330
import Analysis.ContourCertificates.Outer.Block1331
import Analysis.ContourCertificates.Outer.Block1332
import Analysis.ContourCertificates.Outer.Block1333
import Analysis.ContourCertificates.Outer.Block1334
import Analysis.ContourCertificates.Outer.Block1335

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch166

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1328.cells ++
  DirichletL.ContourCertificates.Outer.Block1329.cells ++
  DirichletL.ContourCertificates.Outer.Block1330.cells ++
  DirichletL.ContourCertificates.Outer.Block1331.cells ++
  DirichletL.ContourCertificates.Outer.Block1332.cells ++
  DirichletL.ContourCertificates.Outer.Block1333.cells ++
  DirichletL.ContourCertificates.Outer.Block1334.cells ++
  DirichletL.ContourCertificates.Outer.Block1335.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1328.cells_bounded, DirichletL.ContourCertificates.Outer.Block1329.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1330.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1331.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1332.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1333.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1334.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1335.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch166
