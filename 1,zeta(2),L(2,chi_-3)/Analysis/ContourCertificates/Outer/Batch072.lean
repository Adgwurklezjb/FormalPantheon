import Analysis.ContourCertificates.Outer.Block0576
import Analysis.ContourCertificates.Outer.Block0577
import Analysis.ContourCertificates.Outer.Block0578
import Analysis.ContourCertificates.Outer.Block0579
import Analysis.ContourCertificates.Outer.Block0580
import Analysis.ContourCertificates.Outer.Block0581
import Analysis.ContourCertificates.Outer.Block0582
import Analysis.ContourCertificates.Outer.Block0583

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch072

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0576.cells ++
  DirichletL.ContourCertificates.Outer.Block0577.cells ++
  DirichletL.ContourCertificates.Outer.Block0578.cells ++
  DirichletL.ContourCertificates.Outer.Block0579.cells ++
  DirichletL.ContourCertificates.Outer.Block0580.cells ++
  DirichletL.ContourCertificates.Outer.Block0581.cells ++
  DirichletL.ContourCertificates.Outer.Block0582.cells ++
  DirichletL.ContourCertificates.Outer.Block0583.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0576.cells_bounded, DirichletL.ContourCertificates.Outer.Block0577.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0578.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0579.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0580.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0581.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0582.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0583.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch072
