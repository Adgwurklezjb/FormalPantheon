import Analysis.ContourCertificates.Outer.Block0448
import Analysis.ContourCertificates.Outer.Block0449
import Analysis.ContourCertificates.Outer.Block0450
import Analysis.ContourCertificates.Outer.Block0451
import Analysis.ContourCertificates.Outer.Block0452
import Analysis.ContourCertificates.Outer.Block0453
import Analysis.ContourCertificates.Outer.Block0454
import Analysis.ContourCertificates.Outer.Block0455

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch056

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0448.cells ++
  DirichletL.ContourCertificates.Outer.Block0449.cells ++
  DirichletL.ContourCertificates.Outer.Block0450.cells ++
  DirichletL.ContourCertificates.Outer.Block0451.cells ++
  DirichletL.ContourCertificates.Outer.Block0452.cells ++
  DirichletL.ContourCertificates.Outer.Block0453.cells ++
  DirichletL.ContourCertificates.Outer.Block0454.cells ++
  DirichletL.ContourCertificates.Outer.Block0455.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0448.cells_bounded, DirichletL.ContourCertificates.Outer.Block0449.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0450.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0451.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0452.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0453.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0454.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0455.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch056
