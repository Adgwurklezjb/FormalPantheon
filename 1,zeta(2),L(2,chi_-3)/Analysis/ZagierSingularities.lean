import Analysis.ZagierODEPolynomials

/-!
Singular factors in CDT v2, proof of Lemma `14functions`, equation `explicitode`.
The candidate assembly uses the algebraic bounds preceding equation `b3eq`;
the local pole-order argument that supplies those bounds remains separate.
-/

namespace DirichletL

open Polynomial

theorem eval_zero_zagierSingularCubic : zagierSingularCubic.eval 0 = -1 := by
  norm_num [zagierSingularCubic]

theorem eval_four_zagierSingularCubic : zagierSingularCubic.eval 4 = 7735 := by
  norm_num [zagierSingularCubic]

theorem eval_neg_one_div_seventy_two_zagierSingularCubic :
    zagierSingularCubic.eval (-1 / 72) = -3451 / 1296 := by
  norm_num [zagierSingularCubic]

/-- The cubic singular factor has no repeated roots. -/
theorem zagierSingularCubic_separable : zagierSingularCubic.Separable := by
  have h : (-3897936 * X + 2909012) * zagierSingularCubic +
      (1299312 * X ^ 2 - 1336606 * X + 776401) * zagierSingularCubic.derivative =
      (88706306 : ℂ[X]) := by
    simp only [zagierSingularCubic, derivative_add, derivative_sub, derivative_neg,
      derivative_one, derivative_mul, derivative_ofNat, derivative_X, derivative_pow,
      C_eq_natCast, zero_mul, zero_add, mul_one, pow_one]
    ring
  rw [separable_def']
  refine ⟨C (1 / 88706306) * (-3897936 * X + 2909012),
    C (1 / 88706306) * (1299312 * X ^ 2 - 1336606 * X + 776401), ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_add, h]
  change C (1 / 88706306) * C 88706306 = C 1
  rw [← map_mul]
  norm_num

theorem zagierSingularCubic_squarefree : Squarefree zagierSingularCubic :=
  zagierSingularCubic_separable.squarefree

theorem eval_derivative_zagierSingularCubic_ne_zero {z : ℂ}
    (hz : zagierSingularCubic.eval z = 0) :
    zagierSingularCubic.derivative.eval z ≠ 0 :=
  zagierSingularCubic_separable.eval₂_derivative_ne_zero (RingHom.id ℂ) hz

theorem rootMultiplicity_zagierSingularCubic {z : ℂ}
    (hz : zagierSingularCubic.eval z = 0) :
    zagierSingularCubic.rootMultiplicity z = 1 := by
  have hpos := (rootMultiplicity_pos zagierSingularCubic_separable.ne_zero).mpr hz
  have hle := rootMultiplicity_le_one_of_separable zagierSingularCubic_separable z
  omega

theorem ne_rational_singularities_of_eval_zagierSingularCubic_eq_zero {z : ℂ}
    (hz : zagierSingularCubic.eval z = 0) : z ≠ 0 ∧ z ≠ 4 ∧ z ≠ -1 / 72 := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · norm_num [eval_zero_zagierSingularCubic] at hz
  · norm_num [eval_four_zagierSingularCubic] at hz
  · rw [eval_neg_one_div_seventy_two_zagierSingularCubic] at hz
    norm_num at hz

/-- The finite singular set of CDT equation `explicitode`. -/
theorem eval_zagierODECoeff_four_eq_zero_iff (z : ℂ) :
    (zagierODECoeff 4).eval z = 0 ↔
      z = 0 ∨ z = 4 ∨ z = -1 / 72 ∨ zagierSingularCubic.eval z = 0 := by
  have hlinear : 1 + (72 : ℂ) * z = 0 ↔ z = -1 / 72 := by
    constructor
    · intro h
      linear_combination (1 / 72 : ℂ) * h
    · rintro rfl
      norm_num
  change (((X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic).eval z = 0) ↔ _
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_ofNat, eval_add, eval_one,
    mul_eq_zero, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0), sub_eq_zero, hlinear]
  tauto

private theorem rootMultiplicity_of_factor {p q : ℂ[X]} {a : ℂ} {n : ℕ}
    (hp : p = q * (X - C a) ^ n) (hq : q.eval a ≠ 0) : p.rootMultiplicity a = n := by
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  rw [hp, rootMultiplicity_mul_X_sub_C_pow hq0, rootMultiplicity_eq_zero hq, zero_add]

theorem rootMultiplicity_zagierODECoeff_four_zero :
    (zagierODECoeff 4).rootMultiplicity 0 = 3 := by
  apply rootMultiplicity_of_factor
    (q := (X - 4) ^ 2 * (1 + 72 * X) * zagierSingularCubic)
  · change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic = _
    simp only [map_zero, sub_zero]
    ring
  · norm_num [zagierSingularCubic]

theorem rootMultiplicity_zagierODECoeff_four_four :
    (zagierODECoeff 4).rootMultiplicity 4 = 2 := by
  apply rootMultiplicity_of_factor (q := X ^ 3 * (1 + 72 * X) * zagierSingularCubic)
  · change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic = _
    simp only [map_ofNat]
    ring
  · norm_num [zagierSingularCubic]

theorem rootMultiplicity_zagierODECoeff_four_neg_one_div_seventy_two :
    (zagierODECoeff 4).rootMultiplicity (-1 / 72) = 1 := by
  have h72 : (1 + 72 * X : ℂ[X]) = C 72 * (X - C (-1 / 72)) := by
    rw [mul_sub, ← map_mul]
    norm_num [map_ofNat]
    ring
  apply rootMultiplicity_of_factor
    (q := (X - 4) ^ 2 * X ^ 3 * C 72 * zagierSingularCubic)
  · change (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic = _
    rw [h72, pow_one]
    ring
  · norm_num [zagierSingularCubic]

theorem rootMultiplicity_zagierODECoeff_four_of_cubic_root {z : ℂ}
    (hz : zagierSingularCubic.eval z = 0) :
    (zagierODECoeff 4).rootMultiplicity z = 1 := by
  obtain ⟨hz0, hz4, hz72⟩ := ne_rational_singularities_of_eval_zagierSingularCubic_eq_zero hz
  let T : ℂ[X] := (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X)
  have h72 : 1 + (72 : ℂ) * z ≠ 0 := by
    intro h
    apply hz72
    linear_combination (1 / 72 : ℂ) * h
  have hT : T.eval z ≠ 0 := by simp [T, sub_ne_zero.mpr hz4, hz0, h72]
  have hT0 : T ≠ 0 := by intro h; rw [h, eval_zero] at hT; exact hT rfl
  change (T * zagierSingularCubic).rootMultiplicity z = 1
  rw [rootMultiplicity_mul (mul_ne_zero hT0 zagierSingularCubic_separable.ne_zero),
    rootMultiplicity_eq_zero hT, rootMultiplicity_zagierSingularCubic hz, zero_add]

theorem natDegree_zagierSingularCubic : zagierSingularCubic.natDegree = 3 := by
  unfold zagierSingularCubic
  compute_degree!
  norm_num [coeff_one]

theorem natDegree_zagierAdjointSeed : zagierAdjointSeed.natDegree = 5 := by
  unfold zagierAdjointSeed
  compute_degree!

theorem zagierAdjointSeed_ne_zero : zagierAdjointSeed ≠ 0 := by
  intro h
  have hd := natDegree_zagierAdjointSeed
  rw [h] at hd
  norm_num at hd

theorem natDegree_le_of_zagierAdjointSeed_mul (Q : ℂ[X])
    (h : (zagierAdjointSeed * Q).natDegree ≤ 7) : Q.natDegree ≤ 2 := by
  by_cases hQ : Q = 0
  · simp [hQ]
  rw [natDegree_mul zagierAdjointSeed_ne_zero hQ, natDegree_zagierAdjointSeed] at h
  omega

/-- Assemble the numerator in CDT equation `b3eq` from its local algebraic bounds. -/
theorem exists_zagierAdjointCandidate (N : ℂ[X])
    (h0 : X ^ 2 ∣ N) (h4 : (X - 4) ^ 2 ∣ N) (h72 : 1 + 72 * X ∣ N)
    (hdeg : N.natDegree ≤ 7) :
    ∃ Q : ℂ[X], Q.natDegree ≤ 2 ∧ N = zagierAdjointSeed * Q := by
  have hc04 : IsCoprime (X : ℂ[X]) (X - 4) := by
    simpa using isCoprime_X_sub_C_of_isUnit_sub
      (show IsUnit ((0 : ℂ) - 4) by norm_num)
  have hc072 : IsCoprime (X : ℂ[X]) (1 + 72 * X) :=
    isCoprime_one_right.add_mul_right_right 72
  have hc472 : IsCoprime (X - 4 : ℂ[X]) (1 + 72 * X) := by
    have hc : IsCoprime (X - 4 : ℂ[X]) 289 := by
      refine ⟨0, C (1 / 289), ?_⟩
      simp only [zero_mul, zero_add]
      change C (1 / 289) * C 289 = C 1
      rw [← map_mul]
      norm_num
    convert hc.add_mul_right_right 72 using 1
    ring
  have hc : IsCoprime ((X : ℂ[X]) ^ 2 * (X - 4) ^ 2) (1 + 72 * X) :=
    hc072.pow_left.mul_left hc472.pow_left
  obtain ⟨Q, hQ⟩ := hc.mul_dvd (hc04.pow.mul_dvd h0 h4) h72
  change N = zagierAdjointSeed * Q at hQ
  refine ⟨Q, natDegree_le_of_zagierAdjointSeed_mul Q ?_, hQ⟩
  rwa [← hQ]

end DirichletL
