import Analysis.ContourCertificates.Outer.Block0736
import Analysis.ContourCertificates.Outer.Block0737
import Analysis.ContourCertificates.Outer.Block0738
import Analysis.ContourCertificates.Outer.Block0739
import Analysis.ContourCertificates.Outer.Block0740
import Analysis.ContourCertificates.Outer.Block0741
import Analysis.ContourCertificates.Outer.Block0742
import Analysis.ContourCertificates.Outer.Block0743

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch092

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0736.cells ++
  DirichletL.ContourCertificates.Outer.Block0737.cells ++
  DirichletL.ContourCertificates.Outer.Block0738.cells ++
  DirichletL.ContourCertificates.Outer.Block0739.cells ++
  DirichletL.ContourCertificates.Outer.Block0740.cells ++
  DirichletL.ContourCertificates.Outer.Block0741.cells ++
  DirichletL.ContourCertificates.Outer.Block0742.cells ++
  DirichletL.ContourCertificates.Outer.Block0743.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0736.cells_bounded, DirichletL.ContourCertificates.Outer.Block0737.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0738.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0739.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0740.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0741.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0742.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0743.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch092
