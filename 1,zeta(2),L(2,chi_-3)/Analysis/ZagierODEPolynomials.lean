import Mathlib

/-!
The polynomial data and finite adjoint obstruction in CDT v2, proof of
Lemma `14functions`, equations `explicitode`, `b3eq`, and `degree12`.
This module does not assert the differential equation for `G_A`.
-/

namespace DirichletL

open Polynomial

/-- The cubic factor of the leading coefficient in CDT equation `explicitode`. -/
noncomputable def zagierSingularCubic : ℂ[X] :=
  -1 + 118 * X - 122 * X ^ 2 + 144 * X ^ 3

/-- The five coefficients in CDT equation `explicitode`, in increasing derivative order. -/
noncomputable def zagierODECoeff : Fin 5 → ℂ[X] :=
  ![-18 * (3 + 126 * X - 712 * X ^ 2 + 360 * X ^ 3),
    2 * (-2 - 2761 * X + 141632 * X ^ 2 - 280328 * X ^ 3 + 176412 * X ^ 4 -
      95616 * X ^ 5 + 20736 * X ^ 6),
    2 * X * (-34 - 6353 * X + 690355 * X ^ 2 - 1065613 * X ^ 3 + 867876 * X ^ 4 -
      438336 * X ^ 5 + 72576 * X ^ 6),
    2 * (X - 4) * X ^ 2 * (10 + 204 * X - 118195 * X ^ 2 + 146946 * X ^ 3 -
      142848 * X ^ 4 + 41472 * X ^ 5),
    (X - 4) ^ 2 * X ^ 3 * (1 + 72 * X) * zagierSingularCubic]

/-- The polynomial factor in the candidate `b_3 = K Q / (72 P)` from CDT `b3eq`. -/
noncomputable def zagierAdjointSeed : ℂ[X] := X ^ 2 * (X - 4) ^ 2 * (1 + 72 * X)

/-- Backward adjoint numerators, ordered as `B_0,B_1,B_2,B_3`. -/
noncomputable def zagierAdjointNumerator (Q : ℂ[X]) : Fin 4 → ℂ[X] :=
  let P := zagierSingularCubic
  let B₃ := zagierAdjointSeed * Q
  let B₂ := (48 * X + 5732 * X ^ 2 - 3164 * X ^ 3 + 432 * X ^ 4) * Q -
    zagierAdjointSeed * Q.derivative
  let B₁ := 2 * (-34 - 6353 * X + 690355 * X ^ 2 - 1065613 * X ^ 3 + 867876 * X ^ 4 -
    438336 * X ^ 5 + 72576 * X ^ 6) * Q - P * B₂.derivative + P.derivative * B₂
  let B₀ := zagierODECoeff 1 * P * Q - X * P * B₁.derivative + 2 * X * P.derivative * B₁
  ![B₀, B₁, B₂, B₃]

/-- Numerator of the last adjoint equation, with denominator `72 X^2 P^4`. -/
noncomputable def zagierAdjointResidual (Q : ℂ[X]) : ℂ[X] :=
  X * zagierSingularCubic * (zagierAdjointNumerator Q 0).derivative -
    (zagierSingularCubic + 3 * X * zagierSingularCubic.derivative) *
      zagierAdjointNumerator Q 0 -
    X * zagierSingularCubic ^ 2 * zagierODECoeff 0 * Q

private theorem numerator_two_expansion (q₀ q₁ q₂ : ℂ) :
    zagierAdjointNumerator (C q₀ + C q₁ * X + C q₂ * X ^ 2) 2 =
      C (48 * q₀) * X + C (5732 * q₀ + 32 * q₁) * X ^ 2 +
      C (-3164 * q₀ + 4588 * q₁ + 16 * q₂) * X ^ 3 +
      C (432 * q₀ - 2589 * q₁ + 3444 * q₂) * X ^ 4 +
      C (360 * q₁ - 2014 * q₂) * X ^ 5 + C (288 * q₂) * X ^ 6 := by
  change (48 * X + 5732 * X ^ 2 - 3164 * X ^ 3 + 432 * X ^ 4) * _ -
    zagierAdjointSeed * (C q₀ + C q₁ * X + C q₂ * X ^ 2).derivative = _
  simp only [zagierAdjointSeed, derivative_add, derivative_mul, derivative_pow,
    derivative_C, derivative_X, zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero,
    map_add, map_sub, map_mul, map_neg, map_ofNat, C_eq_natCast]
  ring

private theorem numerator_one_expansion (q₀ q₁ q₂ : ℂ) :
    zagierAdjointNumerator (C q₀ + C q₁ * X + C q₂ * X ^ 2) 1 =
      C (-20 * q₀) + C (-1242 * q₀ - 4 * q₁) * X +
      C (688986 * q₀ - 2718 * q₁ - 20 * q₂) * X ^ 2 +
      C (-1368970 * q₀ + 287586 * q₁ - 2706 * q₂) * X ^ 3 +
      C (2022224 * q₀ - 648576 * q₁ + 153416 * q₂) * X ^ 4 +
      C (-771264 * q₀ + 934116 * q₁ - 338554 * q₂) * X ^ 5 +
      C (82944 * q₀ - 372096 * q₁ + 332772 * q₂) * X ^ 6 +
      C (41472 * q₁ - 156096 * q₂) * X ^ 7 + C (20736 * q₂) * X ^ 8 := by
  change 2 * (-34 - 6353 * X + 690355 * X ^ 2 - 1065613 * X ^ 3 + 867876 * X ^ 4 -
    438336 * X ^ 5 + 72576 * X ^ 6) * _ -
    zagierSingularCubic * (zagierAdjointNumerator (C q₀ + C q₁ * X + C q₂ * X ^ 2) 2).derivative +
    zagierSingularCubic.derivative *
      zagierAdjointNumerator (C q₀ + C q₁ * X + C q₂ * X ^ 2) 2 = _
  rw [numerator_two_expansion]
  simp only [zagierSingularCubic, derivative_add, derivative_sub, derivative_mul,
    derivative_pow, derivative_C, derivative_X, derivative_ofNat, derivative_neg,
    derivative_one, zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero,
    map_add, map_sub, map_mul, map_neg, map_ofNat, C_eq_natCast]
  ring

private theorem numerator_zero_expansion (q₀ q₁ q₂ : ℂ) :
    zagierAdjointNumerator (C q₀ + C q₁ * X + C q₂ * X ^ 2) 0 =
      C (4 * q₀) + C (-912 * q₀) * X +
      C (306804 * q₀ - 858 * q₁ - 36 * q₂) * X ^ 2 +
      C (30989298 * q₀ - 70150 * q₁ - 3068 * q₂) * X ^ 3 +
      C (-101243076 * q₀ - 1210224 * q₁ + 3480 * q₂) * X ^ 4 +
      C (233783604 * q₀ + 19219848 * q₁ - 2921418 * q₂) * X ^ 5 +
      C (-464255760 * q₀ - 57657976 * q₁ + 18812148 * q₂) * X ^ 6 +
      C (528187392 * q₀ - 43293960 * q₁ - 4266324 * q₂) * X ^ 7 +
      C (-123420672 * q₀ + 98283456 * q₁ - 21678720 * q₂) * X ^ 8 +
      C (5971968 * q₀ - 17418240 * q₁ + 7218432 * q₂) * X ^ 9 := by
  change zagierODECoeff 1 * zagierSingularCubic * _ -
    X * zagierSingularCubic *
      (zagierAdjointNumerator (C q₀ + C q₁ * X + C q₂ * X ^ 2) 1).derivative +
    2 * X * zagierSingularCubic.derivative *
      zagierAdjointNumerator (C q₀ + C q₁ * X + C q₂ * X ^ 2) 1 = _
  rw [numerator_one_expansion]
  simp only [zagierSingularCubic, zagierODECoeff, Matrix.cons_val_one, Matrix.cons_val_zero,
    derivative_add, derivative_sub, derivative_mul, derivative_pow, derivative_C,
    derivative_X, derivative_ofNat, derivative_neg, derivative_one,
    zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero,
    map_add, map_sub, map_mul, map_neg, map_ofNat, C_eq_natCast]
  ring

private theorem residual_expansion (q₀ q₁ q₂ : ℂ) :
    zagierAdjointResidual (C q₀ + C q₁ * X + C q₂ * X ^ 2) =
      C (4 * q₀) + C (-1834 * q₀) * X +
      C (8984 * q₀ + 912 * q₁ + 36 * q₂) * X ^ 2 +
      C (-134840676 * q₀ + 332312 * q₁ + 14686 * q₂) * X ^ 3 +
      C (-3131081784 * q₀ + 11602000 * q₁ + 319148 * q₂) * X ^ 4 +
      C (13587783864 * q₀ - 76530416 * q₁ + 10446968 * q₂) * X ^ 5 +
      C (-37811000928 * q₀ + 1937580224 * q₁ - 400828080 * q₂) * X ^ 6 +
      C (30890433936 * q₀ - 7038808928 * q₁ + 3503011224 * q₂) * X ^ 7 +
      C (-36307119264 * q₀ - 37779909056 * q₁ + 3613408560 * q₂) * X ^ 8 +
      C (208615550976 * q₀ + 80554128192 * q₁ - 22019199936 * q₂) * X ^ 9 +
      C (-209461800960 * q₀ - 4057786368 * q₁ + 9560727552 * q₂) * X ^ 10 +
      C (34087993344 * q₀ - 23921215488 * q₁ + 3988740096 * q₂) * X ^ 11 +
      C (-859963392 * q₀ + 2508226560 * q₁ - 905084928 * q₂) * X ^ 12 := by
  rw [zagierAdjointResidual, numerator_zero_expansion]
  simp only [zagierSingularCubic, zagierODECoeff, Matrix.cons_val_zero,
    Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_pow, Polynomial.derivative_C, Polynomial.derivative_X,
    Polynomial.derivative_neg, Polynomial.derivative_ofNat, Polynomial.derivative_one,
    Polynomial.derivative_zero, map_add, map_mul, map_sub, map_neg, map_ofNat, C_eq_natCast, nsmul_eq_mul,
    zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, sub_zero, pow_zero, pow_one]
  ring

private theorem cubic_pow_four : zagierSingularCubic ^ 4 =
    (1 - 472 * X + 84032 * X ^ 2 - 6745456 * X ^ 3 + 214555720 * X ^ 4 -
      847146848 * X ^ 5 + 2246995712 * X ^ 6 - 3847563968 * X ^ 7 +
      5019166480 * X ^ 8 - 4640057856 * X ^ 9 + 3261192192 * X ^ 10 -
      1457160192 * X ^ 11 + 429981696 * X ^ 12 : ℂ[X]) := by
  unfold zagierSingularCubic
  ring

private theorem residual_equation_coeff (q₀ q₁ q₂ a b c : ℂ) (i : ℕ) (hi : i < 6) :
    (zagierAdjointResidual (C q₀ + C q₁ * X + C q₂ * X ^ 2) -
      72 * (C a * X ^ 2 + C b * X + C c) * zagierSingularCubic ^ 4).coeff i =
    (match i with
      | 0 => 4 * q₀ - 72 * c
      | 1 => -1834 * q₀ - 72 * b + 33984 * c
      | 2 => 8984 * q₀ + 912 * q₁ + 36 * q₂ - 72 * a + 33984 * b - 6050304 * c
      | 3 => -134840676 * q₀ + 332312 * q₁ + 14686 * q₂ + 33984 * a - 6050304 * b + 485672832 * c
      | 4 => -3131081784 * q₀ + 11602000 * q₁ + 319148 * q₂ - 6050304 * a + 485672832 * b -
        15448011840 * c
      | _ => 13587783864 * q₀ - 76530416 * q₁ + 10446968 * q₂ + 485672832 * a -
        15448011840 * b + 60994573056 * c) := by
  have hm : 72 * (C a * X ^ 2 + C b * X + C c) * zagierSingularCubic ^ 4 =
      C (72 * a) * (X ^ 2 * zagierSingularCubic ^ 4) +
      C (72 * b) * (X * zagierSingularCubic ^ 4) + C (72 * c) * zagierSingularCubic ^ 4 := by
    simp only [map_mul, map_ofNat, C_eq_natCast]
    ring
  rw [hm, residual_expansion, cubic_pow_four]
  simp only [coeff_sub, coeff_add, coeff_C_mul]
  interval_cases i <;>
    norm_num [Polynomial.coeff_mul_X_pow', Polynomial.coeff_X_pow_mul', Polynomial.coeff_C_mul,
      Polynomial.coeff_X_mul, Polynomial.coeff_X_mul_zero, Polynomial.coeff_X,
      Polynomial.coeff_one] <;> ring

/-- The finite linear algebra at the end of CDT Lemma `14functions`. -/
theorem eq_zero_of_zagierAdjointResidual_eq (q₀ q₁ q₂ a b c : ℂ)
    (h : zagierAdjointResidual (C q₀ + C q₁ * X + C q₂ * X ^ 2) =
      72 * (C a * X ^ 2 + C b * X + C c) * zagierSingularCubic ^ 4) :
    q₀ = 0 ∧ q₁ = 0 ∧ q₂ = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  have he (i : ℕ) (hi : i < 6) := residual_equation_coeff q₀ q₁ q₂ a b c i hi
  rw [h, sub_self] at he
  have h0 := he 0 (by decide)
  have h1 := he 1 (by decide)
  have h2 := he 2 (by decide)
  have h3 := he 3 (by decide)
  have h4 := he 4 (by decide)
  have h5 := he 5 (by decide)
  dsimp only at h0 h1 h2 h3 h4 h5
  simp only [coeff_zero] at h0 h1 h2 h3 h4 h5
  have hq₀ : q₀ = 0 := by
    linear_combination (22500929799574282920 * h0 + 87955171919649280 * h1 +
      218501900580176 * h2 - 338296847342 * h3 - 7753403321 * h4 - 40524462 * h5) /
        967171735939968
  have hq₁ : q₁ = 0 := by
    linear_combination (14752304511481560592536 * h0 + 57634179945210516608 * h1 +
      143041486247692336 * h2 - 221744296472386 * h3 - 5067057133711 * h4 -
        26401499154 * h5) / 1934343471879936
  have hq₂ : q₂ = 0 := by
    linear_combination (139901569013309875752 * h0 + 562880942457696160 * h1 +
      1466265607999184 * h2 - 2132157069782 * h3 - 56405403497 * h4 - 336109986 * h5) /
        40298822330832
  simp only [hq₀, hq₁, hq₂, mul_zero, add_zero, zero_add, sub_zero, zero_sub] at h0 h1 h2
  have hc : c = 0 := by linear_combination h0 / 72
  have hb : b = 0 := by linear_combination (h1 + 33984 * hc) / 72
  have ha : a = 0 := by linear_combination (h2 + 33984 * hb - 6050304 * hc) / 72
  exact ⟨hq₀, hq₁, hq₂, ha, hb, hc⟩

/-- The obstruction applies to every candidate polynomial of degree at most two. -/
theorem eq_zero_of_zagierAdjointResidual_eq_of_natDegree_le (Q : ℂ[X])
    (hQ : Q.natDegree ≤ 2) (a b c : ℂ)
    (h : zagierAdjointResidual Q =
      72 * (C a * X ^ 2 + C b * X + C c) * zagierSingularCubic ^ 4) :
    Q = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 := by
  have hrep : Q = C (Q.coeff 0) + C (Q.coeff 1) * X + C (Q.coeff 2) * X ^ 2 := by
    have he := Q.as_sum_range' 3 (by omega)
    simpa [Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial] using he
  rw [hrep] at h
  obtain ⟨h0, h1, h2, ha, hb, hc⟩ :=
    eq_zero_of_zagierAdjointResidual_eq _ _ _ a b c h
  refine ⟨?_, ha, hb, hc⟩
  rw [hrep, h0, h1, h2]
  simp

end DirichletL
