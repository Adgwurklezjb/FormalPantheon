import Analysis.ContourCertificates.Outer.Block0936
import Analysis.ContourCertificates.Outer.Block0937
import Analysis.ContourCertificates.Outer.Block0938
import Analysis.ContourCertificates.Outer.Block0939
import Analysis.ContourCertificates.Outer.Block0940
import Analysis.ContourCertificates.Outer.Block0941
import Analysis.ContourCertificates.Outer.Block0942
import Analysis.ContourCertificates.Outer.Block0943

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch117

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0936.cells ++
  DirichletL.ContourCertificates.Outer.Block0937.cells ++
  DirichletL.ContourCertificates.Outer.Block0938.cells ++
  DirichletL.ContourCertificates.Outer.Block0939.cells ++
  DirichletL.ContourCertificates.Outer.Block0940.cells ++
  DirichletL.ContourCertificates.Outer.Block0941.cells ++
  DirichletL.ContourCertificates.Outer.Block0942.cells ++
  DirichletL.ContourCertificates.Outer.Block0943.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0936.cells_bounded, DirichletL.ContourCertificates.Outer.Block0937.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0938.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0939.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0940.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0941.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0942.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0943.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch117
