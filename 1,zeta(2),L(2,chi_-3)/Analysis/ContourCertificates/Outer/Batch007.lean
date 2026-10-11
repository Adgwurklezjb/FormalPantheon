import Analysis.ContourCertificates.Outer.Block0056
import Analysis.ContourCertificates.Outer.Block0057
import Analysis.ContourCertificates.Outer.Block0058
import Analysis.ContourCertificates.Outer.Block0059
import Analysis.ContourCertificates.Outer.Block0060
import Analysis.ContourCertificates.Outer.Block0061
import Analysis.ContourCertificates.Outer.Block0062
import Analysis.ContourCertificates.Outer.Block0063

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch007

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0056.cells ++
  DirichletL.ContourCertificates.Outer.Block0057.cells ++
  DirichletL.ContourCertificates.Outer.Block0058.cells ++
  DirichletL.ContourCertificates.Outer.Block0059.cells ++
  DirichletL.ContourCertificates.Outer.Block0060.cells ++
  DirichletL.ContourCertificates.Outer.Block0061.cells ++
  DirichletL.ContourCertificates.Outer.Block0062.cells ++
  DirichletL.ContourCertificates.Outer.Block0063.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0056.cells_bounded, DirichletL.ContourCertificates.Outer.Block0057.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0058.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0059.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0060.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0061.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0062.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0063.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch007
