import Analysis.ContourCertificates.Outer.Block0272
import Analysis.ContourCertificates.Outer.Block0273
import Analysis.ContourCertificates.Outer.Block0274
import Analysis.ContourCertificates.Outer.Block0275
import Analysis.ContourCertificates.Outer.Block0276
import Analysis.ContourCertificates.Outer.Block0277
import Analysis.ContourCertificates.Outer.Block0278
import Analysis.ContourCertificates.Outer.Block0279

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch034

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0272.cells ++
  DirichletL.ContourCertificates.Outer.Block0273.cells ++
  DirichletL.ContourCertificates.Outer.Block0274.cells ++
  DirichletL.ContourCertificates.Outer.Block0275.cells ++
  DirichletL.ContourCertificates.Outer.Block0276.cells ++
  DirichletL.ContourCertificates.Outer.Block0277.cells ++
  DirichletL.ContourCertificates.Outer.Block0278.cells ++
  DirichletL.ContourCertificates.Outer.Block0279.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0272.cells_bounded, DirichletL.ContourCertificates.Outer.Block0273.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0274.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0275.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0276.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0277.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0278.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0279.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch034
