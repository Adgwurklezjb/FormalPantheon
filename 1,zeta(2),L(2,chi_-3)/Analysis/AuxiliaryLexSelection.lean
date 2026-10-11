import Analysis.AuxiliaryMinimalExponent

/-!
Selection of an extreme monomial before CDT v2's coordinate relabeling,
supplied TeX 3998-4028 and 4100-4125. The pre-proof ledger is
-/

namespace DirichletL

open scoped Classical

theorem exists_monotone_lex_le_perm_orbit {d : ℕ}
    (S : Set (Fin d →₀ ℕ)) (hS : S.Nonempty) :
    ∃ n ∈ S, ∃ σ : Equiv.Perm (Fin d),
      Monotone (fun j => n (σ j)) ∧
      ∀ p ∈ S, ∀ τ : Equiv.Perm (Fin d),
        toLex (Finsupp.equivFunOnFinite.symm (fun j => n (σ j))) ≤
          toLex (Finsupp.equivFunOnFinite.symm (fun j => p (τ j))) := by
  let T : Set (Lex (Fin d →₀ ℕ)) := {q | ∃ n ∈ S, ∃ σ : Equiv.Perm (Fin d),
    q = toLex (Finsupp.equivFunOnFinite.symm (fun j => n (σ j)))}
  have hT : T.Nonempty := by
    obtain ⟨n, hn⟩ := hS
    exact ⟨toLex (Finsupp.equivFunOnFinite.symm (fun j => n j)),
      n, hn, Equiv.refl _, rfl⟩
  obtain ⟨q, ⟨n, hn, σ, rfl⟩, hq⟩ :=
    (wellFounded_lt : WellFounded ((· < ·) : Lex (Fin d →₀ ℕ) → _ → Prop)).has_min T hT
  have hleast (p : Fin d →₀ ℕ) (hp : p ∈ S) (τ : Equiv.Perm (Fin d)) :
      toLex (Finsupp.equivFunOnFinite.symm (fun j => n (σ j))) ≤
        toLex (Finsupp.equivFunOnFinite.symm (fun j => p (τ j))) :=
    not_lt.mp (hq _ ⟨p, hp, τ, rfl⟩)
  refine ⟨n, hn, σ, ?_, hleast⟩
  intro i j hij
  rcases lt_or_eq_of_le hij with hij | rfl
  · by_contra h
    have hinv : n (σ j) < n (σ i) := lt_of_not_ge h
    apply (not_lt_of_ge (hleast n hn ((Equiv.swap i j).trans σ)))
    apply Finsupp.lex_lt_iff.mpr
    refine ⟨i, ?_, ?_⟩
    · intro k hki
      change n (σ (Equiv.swap i j k)) = n (σ k)
      rw [Equiv.swap_apply_of_ne_of_ne hki.ne (hki.trans hij).ne]
    · change n (σ (Equiv.swap i j i)) < n (σ i)
      simpa only [Equiv.swap_apply_left] using hinv
  · exact le_rfl

theorem exists_minimal_total_exponent_monotone_lex {d : ℕ} {R : Type*} [CommRing R]
    (F : MvPowerSeries (Fin d) R) (hF : F ≠ 0) :
    ∃ (n : Fin d →₀ ℕ) (σ : Equiv.Perm (Fin d)),
      MvPowerSeries.coeff (R := R) n F ≠ 0 ∧
      (∀ e : Fin d →₀ ℕ, e.degree < n.degree → MvPowerSeries.coeff (R := R) e F = 0) ∧
      Monotone (fun j => n (σ j)) ∧
      ∀ p : Fin d →₀ ℕ, MvPowerSeries.coeff (R := R) p F ≠ 0 → p.degree = n.degree →
        ∀ τ : Equiv.Perm (Fin d),
          toLex (Finsupp.equivFunOnFinite.symm (fun j => n (σ j))) ≤
            toLex (Finsupp.equivFunOnFinite.symm (fun j => p (τ j))) := by
  obtain ⟨n₀, hn₀, hmin₀⟩ := exists_minimal_total_exponent F hF
  let S : Set (Fin d →₀ ℕ) :=
    {p | MvPowerSeries.coeff (R := R) p F ≠ 0 ∧ p.degree = n₀.degree}
  obtain ⟨n, hn, σ, hmono, hleast⟩ :=
    exists_monotone_lex_le_perm_orbit S ⟨n₀, hn₀, rfl⟩
  refine ⟨n, σ, hn.1, ?_, hmono, ?_⟩
  · intro e he
    exact hmin₀ e (he.trans_le hn.2.le)
  · intro p hp hdeg τ
    exact hleast p ⟨hp, hdeg.trans hn.2⟩ τ

end DirichletL
