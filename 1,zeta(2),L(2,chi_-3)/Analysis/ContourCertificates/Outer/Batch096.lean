import Analysis.ContourCertificates.Outer.Block0768
import Analysis.ContourCertificates.Outer.Block0769
import Analysis.ContourCertificates.Outer.Block0770
import Analysis.ContourCertificates.Outer.Block0771
import Analysis.ContourCertificates.Outer.Block0772
import Analysis.ContourCertificates.Outer.Block0773
import Analysis.ContourCertificates.Outer.Block0774
import Analysis.ContourCertificates.Outer.Block0775

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch096

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0768.cells ++
  DirichletL.ContourCertificates.Outer.Block0769.cells ++
  DirichletL.ContourCertificates.Outer.Block0770.cells ++
  DirichletL.ContourCertificates.Outer.Block0771.cells ++
  DirichletL.ContourCertificates.Outer.Block0772.cells ++
  DirichletL.ContourCertificates.Outer.Block0773.cells ++
  DirichletL.ContourCertificates.Outer.Block0774.cells ++
  DirichletL.ContourCertificates.Outer.Block0775.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0768.cells_bounded, DirichletL.ContourCertificates.Outer.Block0769.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0770.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0771.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0772.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0773.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0774.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0775.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch096
