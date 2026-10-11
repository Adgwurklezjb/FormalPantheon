import Arithmetic.ZagierSequences

/-!
Formal power-series differential equation attached to the Zagier recurrence.
This module is algebraic and makes no analytic convergence claim.
-/

namespace DirichletL

/-- The formal power series whose coefficient at `n` is `a n`. -/
noncomputable def generatingSeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk a

/-- The expanded formal differential operator for the Zagier recurrence. -/
noncomputable def generatingODE (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.X ^ 1 * f.derivativeFun.derivativeFun
    - PowerSeries.C (R := ℚ) 10 * (PowerSeries.X ^ 2 * f.derivativeFun.derivativeFun)
    + PowerSeries.C (R := ℚ) 9 * (PowerSeries.X ^ 3 * f.derivativeFun.derivativeFun)
    + f.derivativeFun
    - PowerSeries.C (R := ℚ) 20 * (PowerSeries.X ^ 1 * f.derivativeFun)
    + PowerSeries.C (R := ℚ) 27 * (PowerSeries.X ^ 2 * f.derivativeFun)
    + PowerSeries.C (R := ℚ) 9 * (PowerSeries.X ^ 1 * f)
    - PowerSeries.C (R := ℚ) 3 * f

/-- Coefficients of the formal differential operator, including its initial term. -/
theorem coeff_generatingODE (a : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (generatingODE (generatingSeries a)) =
      if n = 0 then a 1 - 3 * a 0 else
        (n + 1 : ℚ) ^ 2 * a (n + 1) -
          (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * a n +
            9 * (n : ℚ) ^ 2 * a (n - 1) := by
  have coeff_X_mul (p : PowerSeries ℚ) (k : ℕ) :
      (PowerSeries.coeff (R := ℚ) k) (PowerSeries.X * p) =
        if 1 ≤ k then (PowerSeries.coeff (R := ℚ) (k - 1)) p else 0 := by
    rw [mul_comm]
    cases k with
    | zero => simp
    | succ k => simp [PowerSeries.coeff_succ_mul_X]
  by_cases hn : n = 0
  · subst n
    have hder : PowerSeries.constantCoeff (R := ℚ)
        (PowerSeries.mk a).derivativeFun = a 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
        PowerSeries.coeff_derivativeFun]
      simp [generatingSeries]
    simp [generatingODE, generatingSeries,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivativeFun, hder, coeff_X_mul]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp [generatingODE, generatingSeries, PowerSeries.coeff_derivativeFun,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_succ_mul_X, coeff_X_mul, hn,
      Nat.ne_of_gt hn1, pow_one, mul_comm]
    by_cases hn3 : 3 ≤ n
    · have hn2 : 2 ≤ n := by omega
      simp only [if_pos hn1, if_pos hn2, if_pos hn3] at *
      have hnat1 : n - 1 + 1 = n := Nat.sub_add_cancel hn1
      have hnat2 : n - 2 + 2 = n := Nat.sub_add_cancel hn2
      have hnat3 : n - 3 + 3 = n := Nat.sub_add_cancel hn3
      have hnat12 : n - 2 + 1 = n - 1 := by omega
      have hnat31 : n - 3 + 1 + 1 = n - 1 := by omega
      have hcast1 : (n - 1 : ℚ) + 1 = n := by exact_mod_cast hnat1
      have hcast2 : (n - 2 : ℚ) + 1 = n - 1 := by
        exact_mod_cast hnat12
      have hcast3 : (n - 3 : ℚ) + 1 = n - 2 := by
        exact_mod_cast (by omega : n - 3 + 1 = n - 2)
      simp only [Nat.cast_sub (R := ℚ) (by omega : 1 ≤ n),
        Nat.cast_sub (R := ℚ) (by omega : 2 ≤ n),
        Nat.cast_sub (R := ℚ) (by omega : 3 ≤ n)]
      norm_num
      rw [hcast2, hcast3, hnat12, hnat31]
      simp [hnat1, hnat12, hnat31, hcast1, hcast2, hcast3]
      ring
    · by_cases hn2 : 2 ≤ n
      · have hn_eq : n = 2 := by omega
        subst n
        norm_num
        ring
      · have hn_eq : n = 1 := by omega
        subst n
        norm_num
        ring

/-- An inhomogeneous recurrence is represented by its right-hand-side series. -/
theorem generatingSeries_ode_eq_of_recurrence (a r : ℕ → ℚ)
    (h0 : a 1 - 3 * a 0 = r 0)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (n + 1 : ℚ) ^ 2 * a (n + 1) -
          (10 * (n : ℚ) * (n + 1 : ℚ) + 3) * a n +
            9 * (n : ℚ) ^ 2 * a (n - 1) = r n) :
    generatingODE (generatingSeries a) = generatingSeries r := by
  apply PowerSeries.ext
  intro n
  rw [coeff_generatingODE]
  simp only [generatingSeries, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · simp [hn, h0]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    simp [hn, hrec n hn1]

theorem generatingSeries_ode_of_recurrence (a : ℕ → ℚ) (h0 : a 1 = 3 * a 0)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (n + 1 : ℚ) ^ 2 * a (n + 1) - 10 * (n : ℚ) * (n + 1 : ℚ) * a n +
        9 * (n : ℚ) ^ 2 * a (n - 1) = 3 * a n) :
    generatingODE (generatingSeries a) = 0 := by
  apply generatingSeries_ode_eq_of_recurrence a (fun _ => 0)
  · linarith [h0]
  · intro n hn
    nlinarith [hrec n hn]

/-- The formal generating series of the Zagier sequence C. -/
noncomputable def zagierGenerating : PowerSeries ℚ :=
  generatingSeries (fun n => (zagierC n : ℚ))

theorem zagierGenerating_ode : generatingODE zagierGenerating = 0 := by
  apply generatingSeries_ode_of_recurrence
  · norm_num [zagierC_zero, zagierC_one]
  · intro n hn
    simpa using zagierC_recurrence_rational hn

/-- Zagier (2009), equation (3), determines a formal solution from its constant term.
The same comparison applies to any fixed inhomogeneous right side. -/
theorem eq_of_generatingODE_eq {f g : PowerSeries ℚ}
    (h : generatingODE f = generatingODE g)
    (h0 : PowerSeries.constantCoeff (R := ℚ) f = PowerSeries.constantCoeff (R := ℚ) g) : f = g := by
  have hf : generatingSeries (fun n => PowerSeries.coeff (R := ℚ) n f) = f := by
    ext n
    simp [generatingSeries]
  have hg : generatingSeries (fun n => PowerSeries.coeff (R := ℚ) n g) = g := by
    ext n
    simp [generatingSeries]
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
    | succ n =>
      have hn := congrArg (PowerSeries.coeff (R := ℚ) n) h
      rw [← hf, ← hg, coeff_generatingODE, coeff_generatingODE] at hn
      by_cases hn0 : n = 0
      · subst n
        simp only [if_pos rfl, ite_true, ih 0 (by omega)] at hn
        linarith only [hn]
      · simp only [if_neg hn0, ih n (by omega), ih (n - 1) (by omega)] at hn
        have hp : (n + 1 : ℚ) ^ 2 ≠ 0 := by positivity
        apply mul_left_cancel₀ hp
        linarith only [hn]

/-- The normalized solution of the case-C operator is its binomial generating series. -/
theorem eq_zagierGenerating_of_generatingODE_eq_zero {f : PowerSeries ℚ}
    (hf : generatingODE f = 0) (h0 : PowerSeries.constantCoeff (R := ℚ) f = 1) :
    f = zagierGenerating := by
  apply eq_of_generatingODE_eq (hf.trans zagierGenerating_ode.symm)
  rw [h0, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [zagierGenerating, generatingSeries, zagierC_zero]

/-- A finite alternating geometric series in the monomial `X^n`. -/
noncomputable def alternatingGeometricPartial (n m : ℕ) : PowerSeries ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    PowerSeries.monomial (R := ℚ) (n * (j + 1)) ((-1 : ℚ) ^ j)

theorem constantCoeff_alternatingGeometricPartial {n : ℕ} (hn : 0 < n) (N : ℕ) :
    PowerSeries.constantCoeff (R := ℚ) (alternatingGeometricPartial n N) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [alternatingGeometricPartial, PowerSeries.coeff_monomial, Nat.ne_of_gt hn]

theorem coeff_alternatingGeometricPartial_of_le {n m N : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmN : m ≤ N) :
    (PowerSeries.coeff (R := ℚ) m) (alternatingGeometricPartial n N) =
      if n ∣ m then (-1 : ℚ) ^ (m / n - 1) else 0 := by
  by_cases hd : n ∣ m
  · obtain ⟨q, hq⟩ := hd
    have hqpos : 0 < q := by
      by_contra hq0
      have : q = 0 := Nat.eq_zero_of_not_pos hq0
      subst q
      omega
    have hqle : q - 1 < N + 1 := by
      have hqm : q ≤ m := by simpa [hq] using Nat.le_mul_of_pos_left q hn
      omega
    have hmem : q - 1 ∈ Finset.range (N + 1) := Finset.mem_range.mpr hqle
    have huniq : ∀ j ∈ Finset.range (N + 1), j ≠ q - 1 →
        m ≠ n * (j + 1) := by
      intro j hj hjne heq
      have hmul : n * q = n * (j + 1) := hq.symm.trans heq
      have hqj : q = j + 1 := Nat.eq_of_mul_eq_mul_left hn hmul
      omega
    simp only [alternatingGeometricPartial, map_sum, PowerSeries.coeff_monomial]
    rw [Finset.sum_eq_single (q - 1)]
    · have hdiv : n * q / n = q := Nat.mul_div_right q hn
      simp [hq, hdiv, Nat.sub_add_cancel hqpos]
    · intro b hb hbne
      simp [huniq b hb hbne]
    · intro hnot
      exact (hnot hmem).elim
  · simp only [alternatingGeometricPartial, map_sum, PowerSeries.coeff_monomial]
    rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases heq : m = n * (j + 1)
    · exact False.elim (hd ⟨j + 1, heq⟩)
    · simp [heq]

theorem coeff_alternatingGeometricPartial {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (PowerSeries.coeff (R := ℚ) m) (alternatingGeometricPartial n m) =
      if n ∣ m then (-1 : ℚ) ^ (m / n - 1) else 0 :=
  coeff_alternatingGeometricPartial_of_le hn hm le_rfl

end DirichletL
