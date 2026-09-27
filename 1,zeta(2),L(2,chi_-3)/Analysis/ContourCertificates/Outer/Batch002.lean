import Analysis.ContourCertificates.Outer.Block0016
import Analysis.ContourCertificates.Outer.Block0017
import Analysis.ContourCertificates.Outer.Block0018
import Analysis.ContourCertificates.Outer.Block0019
import Analysis.ContourCertificates.Outer.Block0020
import Analysis.ContourCertificates.Outer.Block0021
import Analysis.ContourCertificates.Outer.Block0022
import Analysis.ContourCertificates.Outer.Block0023

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch002

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0016.cells ++
  DirichletL.ContourCertificates.Outer.Block0017.cells ++
  DirichletL.ContourCertificates.Outer.Block0018.cells ++
  DirichletL.ContourCertificates.Outer.Block0019.cells ++
  DirichletL.ContourCertificates.Outer.Block0020.cells ++
  DirichletL.ContourCertificates.Outer.Block0021.cells ++
  DirichletL.ContourCertificates.Outer.Block0022.cells ++
  DirichletL.ContourCertificates.Outer.Block0023.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0016.cells_bounded, DirichletL.ContourCertificates.Outer.Block0017.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0018.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0019.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0020.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0021.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0022.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0023.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch002
