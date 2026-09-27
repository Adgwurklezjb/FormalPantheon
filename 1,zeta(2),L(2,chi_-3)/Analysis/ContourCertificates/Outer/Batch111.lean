import Analysis.ContourCertificates.Outer.Block0888
import Analysis.ContourCertificates.Outer.Block0889
import Analysis.ContourCertificates.Outer.Block0890
import Analysis.ContourCertificates.Outer.Block0891
import Analysis.ContourCertificates.Outer.Block0892
import Analysis.ContourCertificates.Outer.Block0893
import Analysis.ContourCertificates.Outer.Block0894
import Analysis.ContourCertificates.Outer.Block0895

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch111

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0888.cells ++
  DirichletL.ContourCertificates.Outer.Block0889.cells ++
  DirichletL.ContourCertificates.Outer.Block0890.cells ++
  DirichletL.ContourCertificates.Outer.Block0891.cells ++
  DirichletL.ContourCertificates.Outer.Block0892.cells ++
  DirichletL.ContourCertificates.Outer.Block0893.cells ++
  DirichletL.ContourCertificates.Outer.Block0894.cells ++
  DirichletL.ContourCertificates.Outer.Block0895.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0888.cells_bounded, DirichletL.ContourCertificates.Outer.Block0889.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0890.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0891.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0892.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0893.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0894.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0895.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch111
