import Analysis.ContourCertificates.Outer.Block1200
import Analysis.ContourCertificates.Outer.Block1201
import Analysis.ContourCertificates.Outer.Block1202
import Analysis.ContourCertificates.Outer.Block1203
import Analysis.ContourCertificates.Outer.Block1204
import Analysis.ContourCertificates.Outer.Block1205
import Analysis.ContourCertificates.Outer.Block1206
import Analysis.ContourCertificates.Outer.Block1207

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch150

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1200.cells ++
  DirichletL.ContourCertificates.Outer.Block1201.cells ++
  DirichletL.ContourCertificates.Outer.Block1202.cells ++
  DirichletL.ContourCertificates.Outer.Block1203.cells ++
  DirichletL.ContourCertificates.Outer.Block1204.cells ++
  DirichletL.ContourCertificates.Outer.Block1205.cells ++
  DirichletL.ContourCertificates.Outer.Block1206.cells ++
  DirichletL.ContourCertificates.Outer.Block1207.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1200.cells_bounded, DirichletL.ContourCertificates.Outer.Block1201.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1202.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1203.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1204.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1205.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1206.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1207.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch150
