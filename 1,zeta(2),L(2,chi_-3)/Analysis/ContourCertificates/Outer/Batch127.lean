import Analysis.ContourCertificates.Outer.Block1016
import Analysis.ContourCertificates.Outer.Block1017
import Analysis.ContourCertificates.Outer.Block1018
import Analysis.ContourCertificates.Outer.Block1019
import Analysis.ContourCertificates.Outer.Block1020
import Analysis.ContourCertificates.Outer.Block1021
import Analysis.ContourCertificates.Outer.Block1022
import Analysis.ContourCertificates.Outer.Block1023

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch127

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block1016.cells ++
  DirichletL.ContourCertificates.Outer.Block1017.cells ++
  DirichletL.ContourCertificates.Outer.Block1018.cells ++
  DirichletL.ContourCertificates.Outer.Block1019.cells ++
  DirichletL.ContourCertificates.Outer.Block1020.cells ++
  DirichletL.ContourCertificates.Outer.Block1021.cells ++
  DirichletL.ContourCertificates.Outer.Block1022.cells ++
  DirichletL.ContourCertificates.Outer.Block1023.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block1016.cells_bounded, DirichletL.ContourCertificates.Outer.Block1017.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1018.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1019.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1020.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1021.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1022.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block1023.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch127
