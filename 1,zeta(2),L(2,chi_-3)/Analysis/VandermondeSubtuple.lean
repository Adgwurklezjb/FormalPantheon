import Comparator.Statement

/-!
Increasing block enumeration for the Vandermonde multiplier in CDT v2,
supplied TeX 4069-4092. The native determinant sign and empty blocks are
-/

namespace DirichletL

theorem map_orderEmbOfFin_Ioi {d : ℕ} (s : Finset (Fin d)) (i : Fin s.card) :
    (Finset.Ioi i).map (s.orderEmbOfFin rfl).toEmbedding =
      s.filter (fun j => s.orderEmbOfFin rfl i < j) := by
  classical
  ext j
  simp only [Finset.mem_map, Finset.mem_Ioi, Finset.mem_filter]
  constructor
  · rintro ⟨k, hik, rfl⟩
    exact ⟨s.orderEmbOfFin_mem rfl k, (s.orderEmbOfFin rfl).strictMono hik⟩
  · rintro ⟨hj, hij⟩
    let k := (s.orderIsoOfFin rfl).symm ⟨j, hj⟩
    have hk : s.orderEmbOfFin rfl k = j :=
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨j, hj⟩)
    refine ⟨k, ?_, hk⟩
    exact (s.orderEmbOfFin rfl).lt_iff_lt.mp (by simpa only [hk] using hij)

theorem det_vandermonde_orderEmbOfFin {d : ℕ} {R : Type*} [CommRing R]
    (s : Finset (Fin d)) (z : Fin d → R) :
    (Matrix.vandermonde (fun i => z (s.orderEmbOfFin rfl i))).det =
      ∏ i ∈ s, ∏ j ∈ s with i < j, (z j - z i) := by
  classical
  rw [Matrix.det_vandermonde]
  calc
    (∏ i : Fin s.card, ∏ j ∈ Finset.Ioi i,
        (z (s.orderEmbOfFin rfl j) - z (s.orderEmbOfFin rfl i))) =
        ∏ i : Fin s.card, ∏ j ∈ s with s.orderEmbOfFin rfl i < j,
          (z j - z (s.orderEmbOfFin rfl i)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← map_orderEmbOfFin_Ioi s i, Finset.prod_map]
      rfl
    _ = ∏ i ∈ s, ∏ j ∈ s with i < j, (z j - z i) := by
      simpa only [Finset.map_orderEmbOfFin_univ] using
        (Finset.prod_map Finset.univ (s.orderEmbOfFin rfl).toEmbedding
          (fun i => ∏ j ∈ s with i < j, (z j - z i))).symm

end DirichletL
