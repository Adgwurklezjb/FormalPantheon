import Analysis.BlockVandermondePolynomial
import Analysis.VandermondeCoefficient

/-!
The same block polynomial on the coefficient side of CDT v2,
supplied TeX 4092-4130, and published UDC Section 2.5.25. The exact
coercion and shift precede these proofs in
-/

namespace DirichletL

theorem blockVandermondePolynomial_minimum_coefficient {d : ℕ} {κ R : Type*}
    [DecidableEq κ] [CommRing R] [IsDomain R] (b : Fin d → κ) (M : ℕ) :
    let q := ∑ ij ∈ blockVandermondePairs b, M • Finsupp.single ij.2 (1 : ℕ)
    let W := (blockVandermondePolynomial (R := R) b M : MvPowerSeries (Fin d) R)
    MvPowerSeries.coeff (R := R) q W = 1 ∧
      (∀ e : Fin d →₀ ℕ, e.degree < q.degree → MvPowerSeries.coeff (R := R) e W = 0) ∧
      MvPowerSeries.lexOrder W = toLex q := by
  simpa only [coe_blockVandermondePolynomial] using
    vandermondeProduct_minimum_coefficient (R := R) (blockVandermondePairs b)
      (fun ij hij => ((mem_blockVandermondePairs b ij).mp hij).1) M

theorem blockVandermondePolynomial_ne_zero {d : ℕ} {κ R : Type*}
    [DecidableEq κ] [CommRing R] [IsDomain R] (b : Fin d → κ) (M : ℕ) :
    blockVandermondePolynomial (R := R) b M ≠ 0 := by
  obtain ⟨hc, _, _⟩ := blockVandermondePolynomial_minimum_coefficient (R := R) b M
  intro hW
  simp only [hW, MvPolynomial.coe_zero, map_zero, zero_ne_one] at hc

theorem coeff_blockVandermondePolynomial_mul_of_min_total_lex {d : ℕ} {κ R : Type*}
    [DecidableEq κ] [CommRing R] [IsDomain R] (b : Fin d → κ) (M : ℕ)
    (G : MvPowerSeries (Fin d) R) (p : Fin d →₀ ℕ)
    (hp : MvPowerSeries.coeff (R := R) p G ≠ 0)
    (hG : ∀ e : Fin d →₀ ℕ, e.degree < p.degree → MvPowerSeries.coeff (R := R) e G = 0)
    (hpmin : ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) e G ≠ 0 → e.degree = p.degree →
      toLex p ≤ toLex e) :
    MvPowerSeries.coeff (R := R)
        (p + ∑ ij ∈ blockVandermondePairs b, M • Finsupp.single ij.2 1)
        ((blockVandermondePolynomial (R := R) b M : MvPowerSeries (Fin d) R) * G) =
      MvPowerSeries.coeff (R := R) p G := by
  rw [coe_blockVandermondePolynomial]
  exact coeff_vandermondeProduct_mul_of_min_total_lex (blockVandermondePairs b)
    (fun ij hij => ((mem_blockVandermondePairs b ij).mp hij).1) M G p hp hG hpmin

end DirichletL
