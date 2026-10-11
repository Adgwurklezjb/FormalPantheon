import Analysis.ScaledIntervalBasic

/-!
Signed multiplication for exact CDT contour enclosures (v2, TeX 8384-8404).
-/

namespace DirichletL

theorem mul_mem_Icc_corners {a b c d x y : ℝ} (hx : x ∈ Set.Icc a b)
    (hy : y ∈ Set.Icc c d) :
    x * y ∈ Set.Icc (min (min (a * c) (a * d)) (min (b * c) (b * d)))
      (max (max (a * c) (a * d)) (max (b * c) (b * d))) := by
  have hscalar {l u z : ℝ} (hz : z ∈ Set.Icc l u) (t : ℝ) :
      z * t ∈ Set.Icc (min (l * t) (u * t)) (max (l * t) (u * t)) := by
    rcases le_total 0 t with ht | ht
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hz.1 ht),
        (mul_le_mul_of_nonneg_right hz.2 ht).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hz.2 ht),
        (mul_le_mul_of_nonpos_right hz.1 ht).trans (le_max_left _ _)⟩
  have ha := hscalar hy a
  have hb := hscalar hy b
  have hxy := hscalar hx y
  simp only [mul_comm y, mul_comm c, mul_comm d] at ha hb
  exact ⟨(min_le_min ha.1 hb.1).trans hxy.1,
    hxy.2.trans (max_le_max ha.2 hb.2)⟩

namespace ScaledInterval

/-- The four signed corner products, rounded outward to the common scale. -/
def mul (D : ℕ) (I J : NonemptyInterval ℤ) : NonemptyInterval ℤ :=
  let l := min (min (I.fst * J.fst) (I.fst * J.snd))
    (min (I.snd * J.fst) (I.snd * J.snd))
  let u := max (max (I.fst * J.fst) (I.fst * J.snd))
    (max (I.snd * J.fst) (I.snd * J.snd))
  NonemptyInterval.pure (l / (D : ℤ)) ⊔ NonemptyInterval.pure (-((-u) / (D : ℤ)))

theorem mul_mem {D : ℕ} (hD : 0 < D) {I J : NonemptyInterval ℤ} {x y : ℝ}
    (hx : x ∈ denote D I) (hy : y ∈ denote D J) :
    x * y ∈ denote D (mul D I J) := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hDi : (0 : ℤ) < D := by exact_mod_cast hD
  rw [mem_denote_iff hD] at hx hy
  have hxy := mul_mem_Icc_corners hx hy
  let l := min (min (I.fst * J.fst) (I.fst * J.snd))
    (min (I.snd * J.fst) (I.snd * J.snd))
  let u := max (max (I.fst * J.fst) (I.fst * J.snd))
    (max (I.snd * J.fst) (I.snd * J.snd))
  have heq : (D : ℝ) * x * ((D : ℝ) * y) = (D : ℝ) * ((D : ℝ) * (x * y)) := by ring
  have hl : (l : ℝ) ≤ (D : ℝ) * ((D : ℝ) * (x * y)) := by
    simpa only [l, Int.cast_min, Int.cast_mul, heq] using hxy.1
  have hu : (D : ℝ) * ((D : ℝ) * (x * y)) ≤ (u : ℝ) := by
    simpa only [u, Int.cast_max, Int.cast_mul, heq] using hxy.2
  apply mem_denote_hull hD
  · calc
      _ ≤ (l : ℝ) / (D : ℝ) := int_ediv_le_real_div l D hDi
      _ ≤ _ := (div_le_iff₀ hDr).2 (by nlinarith [hl])
  · calc
      _ ≤ (u : ℝ) / (D : ℝ) := (le_div_iff₀ hDr).2 (by nlinarith [hu])
      _ ≤ _ := real_div_le_neg_int_ediv_neg u D hDi

/-- Square an interval and intersect its enclosure with the nonnegative half-line. -/
def square (D : ℕ) (I : NonemptyInterval ℤ) : NonemptyInterval ℤ :=
  NonemptyInterval.map ⟨fun z => max 0 z, fun _ _ h => max_le_max_left 0 h⟩ (mul D I I)

theorem square_mem {D : ℕ} (hD : 0 < D) {I : NonemptyInterval ℤ} {x : ℝ}
    (hx : x ∈ denote D I) : x ^ 2 ∈ denote D (square D I) := by
  have hm := mul_mem hD hx hx
  rw [mem_denote_iff hD] at hm ⊢
  change ((max 0 (mul D I I).fst : ℤ) : ℝ) ≤ D * x ^ 2 ∧
    D * x ^ 2 ≤ ((max 0 (mul D I I).snd : ℤ) : ℝ)
  push_cast
  constructor
  · exact max_le (by positivity) (by simpa only [pow_two] using hm.1)
  · exact le_trans (by simpa only [pow_two] using hm.2) (le_max_right _ _)

end ScaledInterval
end DirichletL
