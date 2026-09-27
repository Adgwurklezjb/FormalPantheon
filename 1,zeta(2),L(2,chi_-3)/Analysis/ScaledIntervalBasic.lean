import Arithmetic.IntegerRoundingBounds

/-!
Scaled integer intervals for CDT v2's signed integral, TeX 8384-8404.
The canonical Mathlib interval operations retain exact integer endpoints.
-/

namespace DirichletL.ScaledInterval

/-- The real closed interval represented by integer endpoints at a common scale. -/
def denote (D : ℕ) (I : NonemptyInterval ℤ) : Set ℝ :=
  Set.Icc ((I.fst : ℝ) / D) ((I.snd : ℝ) / D)

theorem mem_denote_iff {D : ℕ} (hD : 0 < D) {I : NonemptyInterval ℤ} {x : ℝ} :
    x ∈ denote D I ↔ (I.fst : ℝ) ≤ D * x ∧ D * x ≤ (I.snd : ℝ) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  simp only [denote, Set.mem_Icc, div_le_iff₀ hDr, le_div_iff₀ hDr, mul_comm x]

theorem mem_denote_hull {D : ℕ} (hD : 0 < D) {l u : ℤ} {x : ℝ}
    (hl : (l : ℝ) ≤ D * x) (hu : D * x ≤ (u : ℝ)) :
    x ∈ denote D (NonemptyInterval.pure l ⊔ NonemptyInterval.pure u) := by
  rw [mem_denote_iff hD]
  constructor
  · exact le_trans (by exact_mod_cast min_le_left l u) hl
  · exact le_trans hu (by exact_mod_cast le_max_right l u)

/-- Outward integer rounding of a rational constant at scale `D`. -/
def rational (D : ℕ) (n d : ℤ) : NonemptyInterval ℤ :=
  NonemptyInterval.pure ((n * (D : ℤ)) / d) ⊔
    NonemptyInterval.pure (-((-(n * (D : ℤ))) / d))

theorem rational_mem {D : ℕ} (hD : 0 < D) (n d : ℤ) (hd : 0 < d) :
    (n : ℝ) / (d : ℝ) ∈ denote D (rational D n d) := by
  apply mem_denote_hull hD
  · calc
      _ ≤ ((n * (D : ℤ) : ℤ) : ℝ) / (d : ℝ) := int_ediv_le_real_div _ _ hd
      _ = _ := by push_cast; ring
  · calc
      _ = ((n * (D : ℤ) : ℤ) : ℝ) / (d : ℝ) := by push_cast; ring
      _ ≤ _ := real_div_le_neg_int_ediv_neg _ _ hd

theorem add_mem {D : ℕ} (hD : 0 < D) {I J : NonemptyInterval ℤ} {x y : ℝ}
    (hx : x ∈ denote D I) (hy : y ∈ denote D J) :
    x + y ∈ denote D (I + J) := by
  rw [mem_denote_iff hD] at hx hy ⊢
  simpa only [NonemptyInterval.fst_add, NonemptyInterval.snd_add, Int.cast_add, mul_add]
    using And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

theorem neg_mem {D : ℕ} (hD : 0 < D) {I : NonemptyInterval ℤ} {x : ℝ}
    (hx : x ∈ denote D I) : -x ∈ denote D (-I) := by
  rw [mem_denote_iff hD] at hx ⊢
  simpa only [NonemptyInterval.fst_neg, NonemptyInterval.snd_neg, Int.cast_neg, mul_neg]
    using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)

theorem sub_mem {D : ℕ} (hD : 0 < D) {I J : NonemptyInterval ℤ} {x y : ℝ}
    (hx : x ∈ denote D I) (hy : y ∈ denote D J) :
    x - y ∈ denote D (I - J) := by
  simpa only [sub_eq_add_neg] using add_mem hD hx (neg_mem hD hy)

end DirichletL.ScaledInterval
