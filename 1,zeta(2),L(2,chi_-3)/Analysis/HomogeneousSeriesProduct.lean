import Analysis.PowerSeriesCoordinates

/-!
Minimum homogeneous coefficients in products for CDT v2's `G coeff` and
the dampened coefficient, supplied TeX 3998-4028 and 4100-4125. The
-/

namespace DirichletL

open scoped Classical

theorem coeff_mul_of_minimal_total {σ R : Type*} [CommRing R]
    (H F : MvPowerSeries σ R) (n : σ →₀ ℕ)
    (hF : ∀ e : σ →₀ ℕ, e.degree < n.degree → MvPowerSeries.coeff (R := R) e F = 0) :
    MvPowerSeries.coeff (R := R) n (H * F) =
      MvPowerSeries.constantCoeff (σ := σ) (R := R) H * MvPowerSeries.coeff (R := R) n F := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single_of_mem (0, n) (by simp)]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rintro ⟨e, k⟩ hek hne
    have hsum : e + k = n := Finset.mem_antidiagonal.mp hek
    have he : e ≠ 0 := by
      intro hz
      apply hne
      simp_all
    have hpos : 0 < e.degree := Nat.pos_of_ne_zero
      (fun h => he ((Finsupp.degree_eq_zero_iff e).mp h))
    have hdeg : e.degree + k.degree = n.degree := by
      simpa only [Finsupp.degree_add] using congrArg Finsupp.degree hsum
    rw [hF k (by omega), mul_zero]

theorem coeff_mul_eq_coeff_homogeneousComponents {σ R : Type*} [CommRing R]
    (F G : MvPowerSeries σ R) (N K : ℕ)
    (hF : ∀ e : σ →₀ ℕ, e.degree < N → MvPowerSeries.coeff (R := R) e F = 0)
    (hG : ∀ e : σ →₀ ℕ, e.degree < K → MvPowerSeries.coeff (R := R) e G = 0)
    (n : σ →₀ ℕ) (hn : n.degree = N + K) :
    MvPowerSeries.coeff (R := R) n (F * G) =
      MvPowerSeries.coeff (R := R) n
        (MvPowerSeries.homogeneousComponent N F * MvPowerSeries.homogeneousComponent K G) := by
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨e, k⟩ hek
  have hsum : e + k = n := Finset.mem_antidiagonal.mp hek
  have hdeg : e.degree + k.degree = N + K := by
    simpa only [Finsupp.degree_add, hn] using congrArg Finsupp.degree hsum
  by_cases he : e.degree = N
  · have hk : k.degree = K := by omega
    simp only [MvPowerSeries.coeff_homogeneousComponent, if_pos he, if_pos hk]
  · rw [MvPowerSeries.coeff_homogeneousComponent, if_neg he, zero_mul]
    by_cases hlt : e.degree < N
    · rw [hF e hlt, zero_mul]
    · rw [hG k (by omega), mul_zero]

theorem lexOrder_homogeneousComponent_eq {d : ℕ} {R : Type*} [CommRing R]
    (F : MvPowerSeries (Fin d) R) (p : Fin d →₀ ℕ)
    (hp : MvPowerSeries.coeff (R := R) p F ≠ 0)
    (hle : ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) e F ≠ 0 → e.degree = p.degree →
      toLex p ≤ toLex e) :
    MvPowerSeries.lexOrder (MvPowerSeries.homogeneousComponent p.degree F) = toLex p := by
  have hcoeff : MvPowerSeries.coeff (R := R) p
      (MvPowerSeries.homogeneousComponent p.degree F) ≠ 0 := by
    simpa only [MvPowerSeries.coeff_homogeneousComponent, ite_true] using hp
  refine le_antisymm (MvPowerSeries.lexOrder_le_of_coeff_ne_zero hcoeff) ?_
  rw [MvPowerSeries.le_lexOrder_iff]
  intro e he
  rw [MvPowerSeries.coeff_homogeneousComponent]
  split_ifs with hdeg
  · by_contra hne
    have hel : toLex e < toLex p := by exact_mod_cast he
    exact (not_lt_of_ge (hle e hne hdeg)) hel
  · rfl

theorem coeff_mul_of_min_total_lex {d : ℕ} {R : Type*} [CommRing R]
    (F G : MvPowerSeries (Fin d) R) (p q : Fin d →₀ ℕ)
    (hp : MvPowerSeries.coeff (R := R) p F ≠ 0) (hq : MvPowerSeries.coeff (R := R) q G ≠ 0)
    (hF : ∀ e : Fin d →₀ ℕ, e.degree < p.degree → MvPowerSeries.coeff (R := R) e F = 0)
    (hG : ∀ e : Fin d →₀ ℕ, e.degree < q.degree → MvPowerSeries.coeff (R := R) e G = 0)
    (hpmin : ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) e F ≠ 0 → e.degree = p.degree →
      toLex p ≤ toLex e)
    (hqmin : ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) e G ≠ 0 → e.degree = q.degree →
      toLex q ≤ toLex e) :
    MvPowerSeries.coeff (R := R) (p + q) (F * G) =
      MvPowerSeries.coeff (R := R) p F * MvPowerSeries.coeff (R := R) q G := by
  rw [coeff_mul_eq_coeff_homogeneousComponents F G p.degree q.degree hF hG
    (p + q) (Finsupp.degree_add p q)]
  rw [MvPowerSeries.coeff_mul_of_add_lexOrder
    (lexOrder_homogeneousComponent_eq F p hp hpmin)
    (lexOrder_homogeneousComponent_eq G q hq hqmin)]
  simp only [MvPowerSeries.coeff_homogeneousComponent, ite_true]

end DirichletL
