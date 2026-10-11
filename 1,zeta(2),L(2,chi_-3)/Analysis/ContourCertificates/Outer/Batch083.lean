import Analysis.ContourCertificates.Outer.Block0664
import Analysis.ContourCertificates.Outer.Block0665
import Analysis.ContourCertificates.Outer.Block0666
import Analysis.ContourCertificates.Outer.Block0667
import Analysis.ContourCertificates.Outer.Block0668
import Analysis.ContourCertificates.Outer.Block0669
import Analysis.ContourCertificates.Outer.Block0670
import Analysis.ContourCertificates.Outer.Block0671

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch083

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0664.cells ++
  DirichletL.ContourCertificates.Outer.Block0665.cells ++
  DirichletL.ContourCertificates.Outer.Block0666.cells ++
  DirichletL.ContourCertificates.Outer.Block0667.cells ++
  DirichletL.ContourCertificates.Outer.Block0668.cells ++
  DirichletL.ContourCertificates.Outer.Block0669.cells ++
  DirichletL.ContourCertificates.Outer.Block0670.cells ++
  DirichletL.ContourCertificates.Outer.Block0671.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0664.cells_bounded, DirichletL.ContourCertificates.Outer.Block0665.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0666.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0667.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0668.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0669.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0670.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0671.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch083
