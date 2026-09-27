import Analysis.VandermondeSubtuple

/-!
The literal block multiplier W in CDT v2, supplied TeX 4069-4130, and
published UDC Sections 2.5.14-2.5.25. Meanings and the coefficient sign
-/

namespace DirichletL

/-- Increasing coordinate pairs with the same block label. -/
def blockVandermondePairs {d : ℕ} {κ : Type*} [DecidableEq κ]
    (b : Fin d → κ) : Finset (Fin d × Fin d) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ b ij.1 = b ij.2)

@[simp]
theorem mem_blockVandermondePairs {d : ℕ} {κ : Type*} [DecidableEq κ]
    (b : Fin d → κ) (ij : Fin d × Fin d) :
    ij ∈ blockVandermondePairs b ↔ ij.1 < ij.2 ∧ b ij.1 = b ij.2 := by
  simp only [blockVandermondePairs, Finset.mem_filter, Finset.mem_univ, true_and]

theorem prod_blockVandermondePairs {d : ℕ} {κ R : Type*}
    [Fintype κ] [DecidableEq κ] [CommMonoid R] (b : Fin d → κ)
    (f : Fin d → Fin d → R) :
    (∏ ij ∈ blockVandermondePairs b, f ij.1 ij.2) =
      ∏ k, ∏ i ∈ Finset.univ with b i = k,
        ∏ j ∈ (Finset.univ.filter (fun j => b j = k)) with i < j, f i j := by
  have hrow : (∏ ij ∈ blockVandermondePairs b, f ij.1 ij.2) =
      ∏ i, ∏ j ∈ Finset.univ with i < j ∧ b i = b j, f i j := by
    simp only [blockVandermondePairs, Finset.prod_filter]
    rw [← Finset.univ_product_univ, Finset.prod_product]
  rw [hrow, ← Finset.prod_fiberwise Finset.univ b
    (fun i => ∏ j ∈ Finset.univ with i < j ∧ b i = b j, f i j)]
  apply Finset.prod_congr rfl
  intro k _
  apply Finset.prod_congr rfl
  intro i hi
  have hbi : b i = k := (Finset.mem_filter.mp hi).2
  apply Finset.prod_congr ?_ (fun _ _ => rfl)
  ext j
  simp [hbi, eq_comm, and_comm]

/-- The product of `(X j - X i)^M` over the increasing pairs in each block. -/
noncomputable def blockVandermondePolynomial {d : ℕ} {κ R : Type*}
    [DecidableEq κ] [CommRing R] (b : Fin d → κ) (M : ℕ) : MvPolynomial (Fin d) R :=
  ∏ ij ∈ blockVandermondePairs b, (MvPolynomial.X ij.2 - MvPolynomial.X ij.1) ^ M

theorem coe_blockVandermondePolynomial {d : ℕ} {κ R : Type*}
    [DecidableEq κ] [CommRing R] (b : Fin d → κ) (M : ℕ) :
    (blockVandermondePolynomial (R := R) b M : MvPowerSeries (Fin d) R) =
      ∏ ij ∈ blockVandermondePairs b,
        (MvPowerSeries.X ij.2 - MvPowerSeries.X ij.1 : MvPowerSeries (Fin d) R) ^ M := by
  change MvPolynomial.coeToMvPowerSeries.ringHom (blockVandermondePolynomial b M) = _
  simp only [blockVandermondePolynomial, map_prod, map_pow, map_sub,
    MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X]

theorem eval_blockVandermondePolynomial {d : ℕ} {κ R : Type*}
    [Fintype κ] [DecidableEq κ] [CommRing R] (b : Fin d → κ) (M : ℕ) (z : Fin d → R) :
    MvPolynomial.eval z (blockVandermondePolynomial b M) =
      ∏ k, (Matrix.vandermonde (fun i => z
        ((Finset.univ.filter (fun j => b j = k)).orderEmbOfFin rfl i))).det ^ M := by
  rw [blockVandermondePolynomial, MvPolynomial.eval_prod]
  simp only [map_pow, map_sub, MvPolynomial.eval_X]
  rw [prod_blockVandermondePairs b (fun i j => (z j - z i) ^ M)]
  apply Finset.prod_congr rfl
  intro k _
  rw [det_vandermonde_orderEmbOfFin]
  simp only [Finset.prod_pow]

end DirichletL
