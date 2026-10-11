import Analysis.ContourCertificates
import Analysis.ContourFourteenContinuation

/-!
The main independence theorem and its standard formulations and irrationality consequence.
-/

namespace DirichletL

/-- The irrationality consequence in CDT v2, Theorem A, conditional on independence. -/
theorem MainTheorem.irrational_lTwoChiMinusThree (h : MainTheorem) :
    Irrational lTwoChiMinusThree := by
  rintro ⟨q, hq⟩
  have hz := h (-q) 0 1 (by simp [← hq])
  exact one_ne_zero hz.2.2

/-- A failed target relation can be cleared to the paper's integer normalization. -/
theorem exists_integer_cdt_relation_of_not_main (h : ¬ MainTheorem) :
    ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) +
          (c : ℝ) * (zetaTwo / 4) = 0 := by
  unfold MainTheorem at h
  push_neg at h
  obtain ⟨r, s, t, hrel, hnz⟩ := h
  let d : ℕ := r.den * s.den * t.den
  let ar : ℤ := r.num * (s.den : ℤ) * (t.den : ℤ)
  let bs : ℤ := s.num * (r.den : ℤ) * (t.den : ℤ)
  let ct : ℤ := t.num * (r.den : ℤ) * (s.den : ℤ)
  have hrden : (r.den : ℤ) ≠ 0 := by
    exact_mod_cast (Rat.den_nz r)
  have hsden : (s.den : ℤ) ≠ 0 := by
    exact_mod_cast (Rat.den_nz s)
  have htden : (t.den : ℤ) ≠ 0 := by
    exact_mod_cast (Rat.den_nz t)
  have hr : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den r).symm
  have hs : (s : ℝ) = (s.num : ℝ) / (s.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den s).symm
  have ht : (t : ℝ) = (t.num : ℝ) / (t.den : ℝ) := by
    exact_mod_cast (Rat.num_div_den t).symm
  have har : (ar : ℝ) = (d : ℝ) * (r : ℝ) := by
    dsimp [ar, d]
    push_cast
    rw [hr]
    field_simp
  have hbs : (bs : ℝ) = (d : ℝ) * (s : ℝ) := by
    dsimp [bs, d]
    push_cast
    rw [hs]
    field_simp
  have hct : (ct : ℝ) = (d : ℝ) * (t : ℝ) := by
    dsimp [ct, d]
    push_cast
    rw [ht]
    field_simp
  have hscaled : (ar : ℝ) + (2 : ℝ) * (ct : ℝ) *
        (lTwoChiMinusThree / 2) + (4 : ℝ) * (bs : ℝ) *
          (zetaTwo / 4) = 0 := by
    rw [har, hbs, hct]
    calc
      (d : ℝ) * (r : ℝ) + (2 : ℝ) * ((d : ℝ) * (t : ℝ)) *
          (lTwoChiMinusThree / 2) + (4 : ℝ) * ((d : ℝ) * (s : ℝ)) *
            (zetaTwo / 4) = (d : ℝ) *
              ((r : ℝ) + (s : ℝ) * zetaTwo + (t : ℝ) *
                lTwoChiMinusThree) := by ring
      _ = 0 := by rw [hrel, mul_zero]
  have hnonzero : ar ≠ 0 ∨ (2 : ℤ) * ct ≠ 0 ∨
      (4 : ℤ) * bs ≠ 0 := by
    by_contra hzero
    push_neg at hzero
    have harz : ar = 0 := hzero.1
    have hctz : ct = 0 := by
      exact (mul_eq_zero.mp hzero.2.1).resolve_left (by norm_num)
    have hbsz : bs = 0 := by
      exact (mul_eq_zero.mp hzero.2.2).resolve_left (by norm_num)
    have hrnum : r.num = 0 := by
      rcases mul_eq_zero.mp harz with hprod | hden
      · rcases mul_eq_zero.mp hprod with hnum | hden
        · exact hnum
        · exact (hsden hden).elim
      · exact (htden hden).elim
    have hsnum : s.num = 0 := by
      rcases mul_eq_zero.mp hbsz with hprod | hden
      · rcases mul_eq_zero.mp hprod with hnum | hden
        · exact hnum
        · exact (hrden hden).elim
      · exact (htden hden).elim
    have htnum : t.num = 0 := by
      rcases mul_eq_zero.mp hctz with hprod | hden
      · rcases mul_eq_zero.mp hprod with hnum | hden
        · exact hnum
        · exact (hrden hden).elim
      · exact (hsden hden).elim
    exact (hnz (Rat.num_eq_zero.mp hrnum) (Rat.num_eq_zero.mp hsnum))
      (Rat.num_eq_zero.mp htnum)
  refine ⟨ar, (2 : ℤ) * ct, (4 : ℤ) * bs, hnonzero, ?_⟩
  simpa only [Int.cast_mul, Int.cast_ofNat] using hscaled

/-- A nontrivial integer relation in CDT's normalization refutes `MainTheorem`. -/
theorem not_main_of_exists_integer_cdt_relation
    (h : ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) +
          (c : ℝ) * (zetaTwo / 4) = 0) : ¬ MainTheorem := by
  rintro hm
  obtain ⟨a, b, c, hnz, hrel⟩ := h
  have hrel' : (a : ℝ) + (((c : ℚ) / 4 : ℚ) : ℝ) * zetaTwo +
      (((b : ℚ) / 2 : ℚ) : ℝ) * lTwoChiMinusThree = 0 := by
    push_cast
    linarith [hrel]
  have hz := hm (a : ℚ) ((c : ℚ) / 4) ((b : ℚ) / 2) hrel'
  rcases hnz with haz | hbz | hcz
  · exact haz (by exact_mod_cast hz.1)
  · exact hbz (by exact_mod_cast (show (b : ℚ) = 0 by linarith [hz.2.2]))
  · exact hcz (by exact_mod_cast (show (c : ℚ) = 0 by linarith [hz.2.1]))

/-- The target proposition is equivalent to the absence of a normalized integer relation. -/
theorem main_iff_no_integer_cdt_relation :
    MainTheorem ↔ ¬ ∃ a b c : ℤ, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
      (a : ℝ) + (b : ℝ) * (lTwoChiMinusThree / 2) +
          (c : ℝ) * (zetaTwo / 4) = 0 := by
  constructor
  · intro hm hrel
    exact (not_main_of_exists_integer_cdt_relation hrel) hm
  · intro hrel
    by_contra hmain
    exact hrel (exists_integer_cdt_relation_of_not_main hmain)

/-- CDT Theorem A, with zeta(2) in the canonical real-series normalization. -/
theorem mainTheorem : MainTheorem := by
  apply main_iff_no_integer_cdt_relation.mpr
  rintro ⟨a, b, c, hne, hrel⟩
  have hn : ¬(a = 0 ∧ b = 0 ∧ c = 0) := by
    rintro ⟨ha, hb, hc⟩
    rcases hne with h | h | h
    · exact h ha
    · exact h hb
    · exact h hc
  exact cdt_contour_no_integer_relation_of_integral_bound
    twoRadiusMaxIntegral_cdtContourMap_le a b c hn hrel

/-- CDT Theorem A as linear independence of the standard ordered family over Q. -/
theorem linearIndependent_one_zetaTwo_lTwoChiMinusThree :
    LinearIndependent ℚ ![(1 : ℝ), zetaTwo, lTwoChiMinusThree] := by
  exact mainTheorem_iff_linearIndependent.mp mainTheorem

/-- CDT Theorem A in its original pi-squared normalization. -/
theorem piSquaredTheorem : PiSquaredTheorem := by
  exact mainTheorem_iff_piSquaredTheorem.mp mainTheorem

/-- The L-value irrationality consequence of CDT Theorem A. -/
theorem irrational_lTwoChiMinusThree : Irrational lTwoChiMinusThree := by
  exact MainTheorem.irrational_lTwoChiMinusThree mainTheorem

end DirichletL
