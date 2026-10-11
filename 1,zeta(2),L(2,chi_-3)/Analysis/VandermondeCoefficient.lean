import Analysis.HomogeneousSeriesProduct

/-!
The extreme coefficient of the Vandermonde multiplier in CDT v2, supplied
TeX 4092-4130, and published UDC Section 2.5.25. The block shift and sign
-/

namespace DirichletL

open scoped Classical

theorem vandermondeProduct_minimum_coefficient {d : ℕ} {R : Type*}
    [CommRing R] [IsDomain R] (P : Finset (Fin d × Fin d))
    (hP : ∀ ij ∈ P, ij.1 < ij.2) (M : ℕ) :
    let q := ∑ ij ∈ P, M • Finsupp.single ij.2 (1 : ℕ)
    let W := ∏ ij ∈ P, (MvPowerSeries.X ij.2 - MvPowerSeries.X ij.1 :
      MvPowerSeries (Fin d) R) ^ M
    MvPowerSeries.coeff (R := R) q W = 1 ∧
      (∀ e : Fin d →₀ ℕ, e.degree < q.degree → MvPowerSeries.coeff (R := R) e W = 0) ∧
      MvPowerSeries.lexOrder W = toLex q := by
  have hmul (F G : MvPowerSeries (Fin d) R) (p q : Fin d →₀ ℕ)
      (hF : MvPowerSeries.coeff (R := R) p F = 1 ∧ (p.degree : ℕ∞) ≤ F.order ∧
        MvPowerSeries.lexOrder F = toLex p)
      (hG : MvPowerSeries.coeff (R := R) q G = 1 ∧ (q.degree : ℕ∞) ≤ G.order ∧
        MvPowerSeries.lexOrder G = toLex q) :
      MvPowerSeries.coeff (R := R) (p + q) (F * G) = 1 ∧
        ((p + q).degree : ℕ∞) ≤ (F * G).order ∧
        MvPowerSeries.lexOrder (F * G) = toLex (p + q) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [MvPowerSeries.coeff_mul_of_add_lexOrder hF.2.2 hG.2.2, hF.1, hG.1, one_mul]
    · simpa only [Finsupp.degree_add, Nat.cast_add] using
        (add_le_add hF.2.1 hG.2.1).trans MvPowerSeries.le_order_mul
    · rw [MvPowerSeries.lexOrder_mul, hF.2.2, hG.2.2, toLex_add, WithTop.coe_add]
  have hone : MvPowerSeries.coeff (R := R) (0 : Fin d →₀ ℕ) (1 : MvPowerSeries (Fin d) R) = 1 ∧
      ((0 : Fin d →₀ ℕ).degree : ℕ∞) ≤ (1 : MvPowerSeries (Fin d) R).order ∧
      MvPowerSeries.lexOrder (1 : MvPowerSeries (Fin d) R) = toLex (0 : Fin d →₀ ℕ) := by
    have hc : MvPowerSeries.coeff (R := R) (0 : Fin d →₀ ℕ)
        (1 : MvPowerSeries (Fin d) R) = 1 := by simp
    refine ⟨hc, by simp, le_antisymm
      (MvPowerSeries.lexOrder_le_of_coeff_ne_zero (hc.trans_ne one_ne_zero)) ?_⟩
    rw [MvPowerSeries.le_lexOrder_iff]
    intro e he
    rw [MvPowerSeries.coeff_one]
    split_ifs with he0
    · subst e
      exact (lt_irrefl _ he).elim
    · rfl
  have hfactor (i j : Fin d) (hij : i < j) :
      MvPowerSeries.coeff (R := R) (Finsupp.single j 1)
          (MvPowerSeries.X j - MvPowerSeries.X i : MvPowerSeries (Fin d) R) = 1 ∧
        ((Finsupp.single j (1 : ℕ)).degree : ℕ∞) ≤
          (MvPowerSeries.X j - MvPowerSeries.X i : MvPowerSeries (Fin d) R).order ∧
        MvPowerSeries.lexOrder
          (MvPowerSeries.X j - MvPowerSeries.X i : MvPowerSeries (Fin d) R) =
            toLex (Finsupp.single j 1) := by
    have hc : MvPowerSeries.coeff (R := R) (Finsupp.single j 1)
        (MvPowerSeries.X j - MvPowerSeries.X i : MvPowerSeries (Fin d) R) = 1 := by
      simp only [map_sub, MvPowerSeries.coeff_index_single_X, ite_true,
        if_neg hij.ne', sub_zero]
    have hji : toLex (Finsupp.single j (1 : ℕ)) < toLex (Finsupp.single i 1) := by
      apply Finsupp.lex_lt_iff.mpr
      refine ⟨i, ?_, ?_⟩
      · intro k hki
        simp [Finsupp.single_apply, hki.ne, hki.ne', (hki.trans hij).ne,
          (hki.trans hij).ne']
      · simp [Finsupp.single_apply, hij.ne, hij.ne']
    refine ⟨hc, MvPowerSeries.nat_le_order ?_, le_antisymm
      (MvPowerSeries.lexOrder_le_of_coeff_ne_zero (hc.trans_ne one_ne_zero)) ?_⟩
    · intro e he
      have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by
        simpa only [Finsupp.degree_single, Nat.lt_one_iff] using he)
      simp [he0, MvPowerSeries.coeff_zero_X]
    · rw [MvPowerSeries.le_lexOrder_iff]
      intro e he
      have he' : toLex e < toLex (Finsupp.single j (1 : ℕ)) := by exact_mod_cast he
      have hej : e ≠ Finsupp.single j 1 := fun h => (lt_irrefl _ (h ▸ he')).elim
      have hei : e ≠ Finsupp.single i 1 := by
        intro h
        exact (not_lt_of_ge hji.le) (h ▸ he')
      simp only [map_sub, MvPowerSeries.coeff_X, if_neg hej, if_neg hei, sub_self]
  have hpow (i j : Fin d) (hij : i < j) (k : ℕ) :
      MvPowerSeries.coeff (R := R) (k • Finsupp.single j 1)
          ((MvPowerSeries.X j - MvPowerSeries.X i : MvPowerSeries (Fin d) R) ^ k) = 1 ∧
        ((k • Finsupp.single j (1 : ℕ)).degree : ℕ∞) ≤
          ((MvPowerSeries.X j - MvPowerSeries.X i : MvPowerSeries (Fin d) R) ^ k).order ∧
        MvPowerSeries.lexOrder
          ((MvPowerSeries.X j - MvPowerSeries.X i : MvPowerSeries (Fin d) R) ^ k) =
            toLex (k • Finsupp.single j 1) := by
    induction k with
    | zero => simpa using hone
    | succ k ih =>
      simpa only [pow_succ, succ_nsmul] using hmul _ _ _ _ ih (hfactor i j hij)
  have hprod :
      MvPowerSeries.coeff (R := R) (∑ ij ∈ P, M • Finsupp.single ij.2 1)
          (∏ ij ∈ P, (MvPowerSeries.X ij.2 - MvPowerSeries.X ij.1 :
            MvPowerSeries (Fin d) R) ^ M) = 1 ∧
        (((∑ ij ∈ P, M • Finsupp.single ij.2 (1 : ℕ)).degree) : ℕ∞) ≤
          (∏ ij ∈ P, (MvPowerSeries.X ij.2 - MvPowerSeries.X ij.1 :
            MvPowerSeries (Fin d) R) ^ M).order ∧
        MvPowerSeries.lexOrder (∏ ij ∈ P, (MvPowerSeries.X ij.2 - MvPowerSeries.X ij.1 :
          MvPowerSeries (Fin d) R) ^ M) = toLex (∑ ij ∈ P, M • Finsupp.single ij.2 1) := by
    induction P using Finset.induction_on with
    | empty => simpa using hone
    | @insert ij P hij ih =>
      have hs := ih (fun v hv => hP v (Finset.mem_insert_of_mem hv))
      have hf := hpow ij.1 ij.2 (hP ij (Finset.mem_insert_self _ _)) M
      simpa only [Finset.prod_insert hij, Finset.sum_insert hij] using hmul _ _ _ _ hf hs
  refine ⟨hprod.1, ?_, hprod.2.2⟩
  intro e he
  exact MvPowerSeries.coeff_of_lt_order
    ((by exact_mod_cast he : (e.degree : ℕ∞) < _).trans_le hprod.2.1)

theorem coeff_vandermondeProduct_mul_of_min_total_lex {d : ℕ} {R : Type*}
    [CommRing R] [IsDomain R] (P : Finset (Fin d × Fin d))
    (hP : ∀ ij ∈ P, ij.1 < ij.2) (M : ℕ) (G : MvPowerSeries (Fin d) R)
    (p : Fin d →₀ ℕ) (hp : MvPowerSeries.coeff (R := R) p G ≠ 0)
    (hG : ∀ e : Fin d →₀ ℕ, e.degree < p.degree → MvPowerSeries.coeff (R := R) e G = 0)
    (hpmin : ∀ e : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) e G ≠ 0 → e.degree = p.degree →
      toLex p ≤ toLex e) :
    MvPowerSeries.coeff (R := R) (p + ∑ ij ∈ P, M • Finsupp.single ij.2 1)
        ((∏ ij ∈ P, (MvPowerSeries.X ij.2 - MvPowerSeries.X ij.1 :
          MvPowerSeries (Fin d) R) ^ M) * G) = MvPowerSeries.coeff (R := R) p G := by
  obtain ⟨hc, hlow, hlex⟩ := vandermondeProduct_minimum_coefficient (R := R) P hP M
  rw [add_comm, coeff_mul_of_min_total_lex _ G _ p (hc.trans_ne one_ne_zero) hp
    hlow hG ?_ hpmin, hc, one_mul]
  intro e he _
  have h := MvPowerSeries.lexOrder_le_of_coeff_ne_zero he
  rw [hlex] at h
  exact_mod_cast h

end DirichletL
