import Analysis.ContourCertificates.Outer.Block0280
import Analysis.ContourCertificates.Outer.Block0281
import Analysis.ContourCertificates.Outer.Block0282
import Analysis.ContourCertificates.Outer.Block0283
import Analysis.ContourCertificates.Outer.Block0284
import Analysis.ContourCertificates.Outer.Block0285
import Analysis.ContourCertificates.Outer.Block0286
import Analysis.ContourCertificates.Outer.Block0287

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch035

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0280.cells ++
  DirichletL.ContourCertificates.Outer.Block0281.cells ++
  DirichletL.ContourCertificates.Outer.Block0282.cells ++
  DirichletL.ContourCertificates.Outer.Block0283.cells ++
  DirichletL.ContourCertificates.Outer.Block0284.cells ++
  DirichletL.ContourCertificates.Outer.Block0285.cells ++
  DirichletL.ContourCertificates.Outer.Block0286.cells ++
  DirichletL.ContourCertificates.Outer.Block0287.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0280.cells_bounded, DirichletL.ContourCertificates.Outer.Block0281.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0282.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0283.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0284.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0285.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0286.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0287.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch035
