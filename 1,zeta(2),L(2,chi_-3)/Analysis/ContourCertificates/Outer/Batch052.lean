import Analysis.ContourCertificates.Outer.Block0416
import Analysis.ContourCertificates.Outer.Block0417
import Analysis.ContourCertificates.Outer.Block0418
import Analysis.ContourCertificates.Outer.Block0419
import Analysis.ContourCertificates.Outer.Block0420
import Analysis.ContourCertificates.Outer.Block0421
import Analysis.ContourCertificates.Outer.Block0422
import Analysis.ContourCertificates.Outer.Block0423

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch052

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0416.cells ++
  DirichletL.ContourCertificates.Outer.Block0417.cells ++
  DirichletL.ContourCertificates.Outer.Block0418.cells ++
  DirichletL.ContourCertificates.Outer.Block0419.cells ++
  DirichletL.ContourCertificates.Outer.Block0420.cells ++
  DirichletL.ContourCertificates.Outer.Block0421.cells ++
  DirichletL.ContourCertificates.Outer.Block0422.cells ++
  DirichletL.ContourCertificates.Outer.Block0423.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0416.cells_bounded, DirichletL.ContourCertificates.Outer.Block0417.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0418.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0419.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0420.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0421.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0422.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0423.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch052
