import Analysis.ContourCertificates.Outer.Block0240
import Analysis.ContourCertificates.Outer.Block0241
import Analysis.ContourCertificates.Outer.Block0242
import Analysis.ContourCertificates.Outer.Block0243
import Analysis.ContourCertificates.Outer.Block0244
import Analysis.ContourCertificates.Outer.Block0245
import Analysis.ContourCertificates.Outer.Block0246
import Analysis.ContourCertificates.Outer.Block0247

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch030

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0240.cells ++
  DirichletL.ContourCertificates.Outer.Block0241.cells ++
  DirichletL.ContourCertificates.Outer.Block0242.cells ++
  DirichletL.ContourCertificates.Outer.Block0243.cells ++
  DirichletL.ContourCertificates.Outer.Block0244.cells ++
  DirichletL.ContourCertificates.Outer.Block0245.cells ++
  DirichletL.ContourCertificates.Outer.Block0246.cells ++
  DirichletL.ContourCertificates.Outer.Block0247.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0240.cells_bounded, DirichletL.ContourCertificates.Outer.Block0241.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0242.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0243.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0244.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0245.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0246.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0247.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch030
