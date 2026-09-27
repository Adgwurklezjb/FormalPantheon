import Analysis.ContourCertificates.Outer.Block0144
import Analysis.ContourCertificates.Outer.Block0145
import Analysis.ContourCertificates.Outer.Block0146
import Analysis.ContourCertificates.Outer.Block0147
import Analysis.ContourCertificates.Outer.Block0148
import Analysis.ContourCertificates.Outer.Block0149
import Analysis.ContourCertificates.Outer.Block0150
import Analysis.ContourCertificates.Outer.Block0151

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch018

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0144.cells ++
  DirichletL.ContourCertificates.Outer.Block0145.cells ++
  DirichletL.ContourCertificates.Outer.Block0146.cells ++
  DirichletL.ContourCertificates.Outer.Block0147.cells ++
  DirichletL.ContourCertificates.Outer.Block0148.cells ++
  DirichletL.ContourCertificates.Outer.Block0149.cells ++
  DirichletL.ContourCertificates.Outer.Block0150.cells ++
  DirichletL.ContourCertificates.Outer.Block0151.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0144.cells_bounded, DirichletL.ContourCertificates.Outer.Block0145.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0146.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0147.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0148.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0149.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0150.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0151.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch018
