import Comparator.Statement

/-!
The exact balanced-map count in CDT v2, supplied TeX 3806-3823.
Partition equivalences by their first component and count the
independent labelings of each fiber using canonical finite equivalences.
-/

namespace DirichletL

open scoped Nat

/-- Equivalences commuting with two maps correspond to equivalences of their matching fibers. -/
def commutingEquivFiberEquiv {A B C : Type*} (f : A → C) (g : B → C) :
    {e : A ≃ B // ∀ a, g (e a) = f a} ≃
      (∀ c, {a : A // f a = c} ≃ {b : B // g b = c}) where
  toFun e c := e.1.subtypeEquiv (by intro a; rw [e.2 a])
  invFun F := ⟨Equiv.ofFiberEquiv F, Equiv.ofFiberEquiv_map F⟩
  left_inv e := by
    apply Subtype.ext
    ext a
    rfl
  right_inv F := by
    funext c
    apply Equiv.ext
    rintro ⟨a, ha⟩
    subst c
    rfl

/-- Each fiber of the first projection of a product is equivalent to its second factor. -/
def prodFstFiberEquiv {A B : Type*} (i : A) :
    {x : A × B // x.1 = i} ≃ B where
  toFun x := x.1.2
  invFun b := ⟨(i, b), rfl⟩
  left_inv := by
    rintro ⟨⟨a, b⟩, ha⟩
    dsimp only at ha
    subst a
    rfl
  right_inv _ := rfl

theorem card_fiber_fst_equiv {m h : ℕ}
    (e : Fin (m * h) ≃ Fin m × Fin h) (i : Fin m) :
    Fintype.card {a : Fin (m * h) // (e a).1 = i} = h := by
  let ef : {a : Fin (m * h) // (e a).1 = i} ≃ Fin h :=
    (e.subtypeEquiv (fun _ => Iff.rfl)).trans (prodFstFiberEquiv i)
  simpa using Fintype.card_congr ef

theorem card_equiv_fst_eq {m h : ℕ} (σ : Fin (m * h) → Fin m)
    (hσ : ∀ i : Fin m, Fintype.card {a : Fin (m * h) // σ a = i} = h) :
    Fintype.card {e : Fin (m * h) ≃ Fin m × Fin h // (fun a => (e a).1) = σ} =
      (h !) ^ m := by
  classical
  let e₁ : {e : Fin (m * h) ≃ Fin m × Fin h // (fun a => (e a).1) = σ} ≃
      {e : Fin (m * h) ≃ Fin m × Fin h // ∀ a, (e a).1 = σ a} :=
    Equiv.subtypeEquivRight (fun _ => ⟨fun he a => congrFun he a, fun he => funext he⟩)
  let e₂ := commutingEquivFiberEquiv σ (Prod.fst : Fin m × Fin h → Fin m)
  have hfib (i : Fin m) :
      Fintype.card ({a : Fin (m * h) // σ a = i} ≃
        {x : Fin m × Fin h // x.1 = i}) = h ! := by
    let ef := (Fintype.equivFinOfCardEq (hσ i)).trans
      (prodFstFiberEquiv (B := Fin h) i).symm
    rw [Fintype.card_equiv ef, hσ i]
  calc
    _ = Fintype.card (∀ i : Fin m, {a : Fin (m * h) // σ a = i} ≃
        {x : Fin m × Fin h // x.1 = i}) := Fintype.card_congr (e₁.trans e₂)
    _ = ∏ _i : Fin m, h ! := by
      rw [Fintype.card_pi]
      exact Finset.prod_congr rfl (fun i _ => hfib i)
    _ = _ := by simp

/-- Assignments of `m * h` coordinates to `m` species, with exactly `h` of each species. -/
def balancedSpeciesIndices (m h : ℕ) : Finset (Fin (m * h) → Fin m) :=
  Finset.univ.filter fun σ => ∀ i : Fin m,
    (Finset.univ.filter (fun a : Fin (m * h) => σ a = i)).card = h

theorem card_balancedSpeciesIndices_mul_factorial (m h : ℕ) :
    (balancedSpeciesIndices m h).card * (h !) ^ m = (m * h)! := by
  classical
  let p : (Fin (m * h) → Fin m) → Prop :=
    fun σ => ∀ i : Fin m, Fintype.card {a : Fin (m * h) // σ a = i} = h
  have hbal : Fintype.card {σ : Fin (m * h) → Fin m // p σ} =
      (balancedSpeciesIndices m h).card := by
    rw [Fintype.card_subtype]
    unfold balancedSpeciesIndices
    congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    dsimp only [p]
    simp only [Fintype.card_subtype]
  have htotal := Fintype.card_congr (Equiv.sigmaSubtypeFiberEquiv
    (fun e : Fin (m * h) ≃ Fin m × Fin h => fun a => (e a).1) p
    (fun e i => card_fiber_fst_equiv e i))
  rw [Fintype.card_sigma] at htotal
  calc
    _ = ∑ _σ : {σ : Fin (m * h) → Fin m // p σ}, (h !) ^ m := by simp [hbal]
    _ = ∑ σ : {σ : Fin (m * h) → Fin m // p σ},
        Fintype.card {e : Fin (m * h) ≃ Fin m × Fin h // (fun a => (e a).1) = σ.1} := by
      exact Finset.sum_congr rfl (fun σ _ => (card_equiv_fst_eq σ.1 σ.2).symm)
    _ = Fintype.card (Fin (m * h) ≃ Fin m × Fin h) := htotal
    _ = _ := by
      simpa using Fintype.card_equiv
        (finProdFinEquiv.symm : Fin (m * h) ≃ Fin m × Fin h)

theorem card_balancedSpeciesIndices_eq_multinomial (m h : ℕ) :
    (balancedSpeciesIndices m h).card =
      Nat.multinomial Finset.univ (fun _ : Fin m => h) := by
  have hm : (h !) ^ m * Nat.multinomial Finset.univ (fun _ : Fin m => h) =
      (m * h)! := by
    simpa using Nat.multinomial_spec Finset.univ (fun _ : Fin m => h)
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.factorial_pos h) m)
  exact (card_balancedSpeciesIndices_mul_factorial m h).trans (by
    simpa only [mul_comm] using hm.symm)

theorem card_balancedSpeciesIndices_pos (m h : ℕ) :
    0 < (balancedSpeciesIndices m h).card := by
  rw [card_balancedSpeciesIndices_eq_multinomial]
  exact Nat.multinomial_pos _ _

end DirichletL
