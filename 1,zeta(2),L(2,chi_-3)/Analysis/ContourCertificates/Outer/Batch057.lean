import Analysis.ContourCertificates.Outer.Block0456
import Analysis.ContourCertificates.Outer.Block0457
import Analysis.ContourCertificates.Outer.Block0458
import Analysis.ContourCertificates.Outer.Block0459
import Analysis.ContourCertificates.Outer.Block0460
import Analysis.ContourCertificates.Outer.Block0461
import Analysis.ContourCertificates.Outer.Block0462
import Analysis.ContourCertificates.Outer.Block0463

/-!
Consecutive outer cells for CDT, author pages 174 and 204.
Complete meanings and exact data precede these proofs in
-/

namespace DirichletL.ContourCertificates.Outer.Batch057

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The consecutive cells of this production batch, assembled without changing their order or pairing. -/
def cells : List ContourGridCell := DirichletL.ContourCertificates.Outer.Block0456.cells ++
  DirichletL.ContourCertificates.Outer.Block0457.cells ++
  DirichletL.ContourCertificates.Outer.Block0458.cells ++
  DirichletL.ContourCertificates.Outer.Block0459.cells ++
  DirichletL.ContourCertificates.Outer.Block0460.cells ++
  DirichletL.ContourCertificates.Outer.Block0461.cells ++
  DirichletL.ContourCertificates.Outer.Block0462.cells ++
  DirichletL.ContourCertificates.Outer.Block0463.cells

/-- All batch cells satisfy their actual complete profile bounds. Coverage and adjacency remain separate obligations. -/
theorem cells_bounded : ∀ cell ∈ cells, ContourGridCell.Bounded (2 ^ 120) 65536 false cell := by
  simp only [cells, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨DirichletL.ContourCertificates.Outer.Block0456.cells_bounded, DirichletL.ContourCertificates.Outer.Block0457.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0458.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0459.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0460.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0461.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0462.cells_bounded⟩, DirichletL.ContourCertificates.Outer.Block0463.cells_bounded⟩

end DirichletL.ContourCertificates.Outer.Batch057
