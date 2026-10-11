import Analysis.MobiusDescent

/-!
The trace polynomials in CDT v2, equation `polysym`, and their coefficient
formula for the already constructed formal Mobius descent.
-/

namespace DirichletL

/-- CDT's trace polynomial, expressed using Mathlib's first-kind Dickson polynomial. -/
noncomputable def mobiusTracePolynomial (n : ℕ) : Polynomial ℚ :=
  (Polynomial.dickson 1 (Polynomial.X : Polynomial ℚ) n).eval Polynomial.X

@[simp]
theorem mobiusTracePolynomial_zero : mobiusTracePolynomial 0 = 2 := by
  norm_num [mobiusTracePolynomial]

@[simp]
theorem mobiusTracePolynomial_one : mobiusTracePolynomial 1 = Polynomial.X := by
  simp [mobiusTracePolynomial]

theorem mobiusTracePolynomial_add_two (n : ℕ) :
    mobiusTracePolynomial (n + 2) =
      Polynomial.X * (mobiusTracePolynomial (n + 1) - mobiusTracePolynomial n) := by
  simp [mobiusTracePolynomial, mul_sub]

/-- Both elementary symmetric functions of the two formal roots equal `y`. -/
theorem X_mul_mobiusInvolutionQ :
    PowerSeries.X * mobiusInvolutionQ = mobiusCoordinateQ := by
  rw [mobiusCoordinateQ_eq]
  simp only [mobiusInvolutionQ, mobiusInvolution, map_neg, map_mul, PowerSeries.map_X]
  ring

/-- The trace evaluation identity needs only the elementary symmetric relation. -/
theorem mobiusTracePolynomial_aeval {R : Type*} [CommRing R] [Algebra ℚ R]
    (x w : R) (h : x + w = x * w) (n : ℕ) :
    Polynomial.aeval (x + w) (mobiusTracePolynomial n) = x ^ n + w ^ n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [mobiusTracePolynomial_zero]
    change Polynomial.aeval (x + w) (Polynomial.C 2) = _
    rw [Polynomial.aeval_C]
    rw [show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one, pow_zero, pow_zero]
  | one => simp
  | more n ih0 ih1 =>
    rw [mobiusTracePolynomial_add_two, map_mul, map_sub, Polynomial.aeval_X, ih1, ih0]
    calc
      (x + w) * (x ^ (n + 1) + w ^ (n + 1) - (x ^ n + w ^ n)) =
          (x + w) * (x ^ (n + 1) + w ^ (n + 1)) -
            (x * w) * (x ^ n + w ^ n) := by rw [← h]; ring
      _ = x ^ (n + 2) + w ^ (n + 2) := by simp only [pow_succ]; ring

private theorem subst_polynomial_eq_aeval (p : Polynomial ℚ) :
    MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) (p : PowerSeries ℚ) =
      Polynomial.aeval mobiusCoordinateQ p := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusCoordinateQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [MvPowerSeries.subst_add hy, hp, hq]
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X,
      MvPowerSeries.subst_mul hy, MvPowerSeries.subst_pow hy]
    have hX : MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ)
        (PowerSeries.X : PowerSeries ℚ) = mobiusCoordinateQ := MvPowerSeries.subst_X hy ()
    have hC : MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ)
        (PowerSeries.C (R := ℚ) a) = PowerSeries.C (R := ℚ) a := by
      rw [← MvPowerSeries.substAlgHom_apply hy]
      exact (MvPowerSeries.substAlgHom hy).commutes a
    simp [hC, hX]

/-- The trace polynomial is the positive formal symmetrization of a monomial. -/
theorem symmetrizedDescent_X_pow (n : ℕ) :
    symmetrizedDescent (PowerSeries.X ^ n) =
      (mobiusTracePolynomial n : PowerSeries ℚ) := by
  apply subst_mobiusCoordinateQ_injective
  rw [subst_symmetrizedDescent, subst_polynomial_eq_aeval]
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusInvolutionQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  change PowerSeries.X ^ n +
      MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) (PowerSeries.X ^ n) = _
  have hX : MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ)
      (PowerSeries.X : PowerSeries ℚ) = mobiusInvolutionQ := MvPowerSeries.subst_X hw ()
  rw [MvPowerSeries.subst_pow hw, hX]
  exact (mobiusTracePolynomial_aeval PowerSeries.X mobiusInvolutionQ
    X_mul_mobiusInvolutionQ.symm n).symm

theorem coeff_mobiusTracePolynomial_eq_zero_of_lt {k n : ℕ} (h : 2 * n < k) :
    (mobiusTracePolynomial k).coeff n = 0 := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero => omega
  | one =>
    have hn : n = 0 := by omega
    subst n
    simp
  | more k ih0 ih1 =>
    rw [mobiusTracePolynomial_add_two]
    cases n with
    | zero => simp
    | succ n =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_sub, ih1 (by omega), ih0 (by omega)]
      simp

theorem coeff_mobiusTracePolynomial_eq_zero_of_gt {k n : ℕ} (h : k < n) :
    (mobiusTracePolynomial k).coeff n = 0 := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero =>
    rw [mobiusTracePolynomial_zero]
    change (Polynomial.C (2 : ℚ)).coeff n = 0
    simp [Polynomial.coeff_C, Nat.ne_of_gt h]
  | one => simp [Polynomial.coeff_X, show (1 : ℕ) ≠ n by omega]
  | more k ih0 ih1 =>
    rw [mobiusTracePolynomial_add_two]
    cases n with
    | zero => omega
    | succ n =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_sub, ih1 (by omega), ih0 (by omega)]
      simp

/-- A uniform exponential bound for every coefficient of a trace polynomial. -/
theorem norm_coeff_mobiusTracePolynomial (k n : ℕ) :
    ‖((mobiusTracePolynomial k).coeff n : ℂ)‖ ≤ (2 : ℝ) ^ (k + 1) := by
  induction k using Nat.twoStepInduction generalizing n with
  | zero =>
    rw [mobiusTracePolynomial_zero]
    change ‖((Polynomial.C (2 : ℚ)).coeff n : ℂ)‖ ≤ _
    rw [Polynomial.coeff_C]
    split_ifs <;> norm_num
  | one =>
    simp only [mobiusTracePolynomial_one, Polynomial.coeff_X]
    split_ifs <;> norm_num
  | more k ih0 ih1 =>
    rw [mobiusTracePolynomial_add_two]
    cases n with
    | zero => simp
    | succ n =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_sub, Rat.cast_sub]
      calc
        _ ≤ ‖((mobiusTracePolynomial (k + 1)).coeff n : ℂ)‖ +
            ‖((mobiusTracePolynomial k).coeff n : ℂ)‖ := norm_sub_le _ _
        _ ≤ 2 ^ (k + 1 + 1) + 2 ^ (k + 1) := add_le_add (ih1 n) (ih0 n)
        _ ≤ 2 ^ (k + 2 + 1) := by
          simp only [pow_succ]
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]

/-- A descended coefficient depends only on the input through twice its index. -/
theorem coeff_mobiusDescent_congr {f g : PowerSeries ℚ} (n : ℕ)
    (h : ∀ k : ℕ, k ≤ 2 * n → PowerSeries.coeff (R := ℚ) k f = PowerSeries.coeff (R := ℚ) k g) :
    PowerSeries.coeff (R := ℚ) n (mobiusDescent f) = PowerSeries.coeff (R := ℚ) n (mobiusDescent g) := by
  simp only [coeff_mobiusDescent]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [mobiusDescentCoeff_eq, mobiusDescentCoeff_eq, h (2 * n) le_rfl]
    congr 2
    apply Finset.sum_congr rfl
    intro k hk
    have hkn := Finset.mem_range.mp hk
    rw [ih k (Finset.mem_range.mp hk) (fun j hj => h j (by omega))]

theorem coeff_symmetrizedDescent_congr {f g : PowerSeries ℚ} (n : ℕ)
    (h : ∀ k : ℕ, k ≤ 2 * n → PowerSeries.coeff (R := ℚ) k f = PowerSeries.coeff (R := ℚ) k g) :
    PowerSeries.coeff (R := ℚ) n (symmetrizedDescent f) =
      PowerSeries.coeff (R := ℚ) n (symmetrizedDescent g) := by
  apply coeff_mobiusDescent_congr
  intro k hk
  change PowerSeries.coeff (R := ℚ) k
      (f + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f) =
    PowerSeries.coeff (R := ℚ) k
      (g + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) g)
  rw [map_add, map_add, h k hk]
  congr 1
  rw [coeff_subst_eq_sum f _ constantCoeff_mobiusInvolutionQ,
    coeff_subst_eq_sum g _ constantCoeff_mobiusInvolutionQ]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (by have := Finset.mem_range.mp hj; omega)]

/-- The finite coefficient formula in CDT equation `polysym`. -/
theorem coeff_symmetrizedDescent_eq_sum (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (symmetrizedDescent f) =
      ∑ k ∈ Finset.range (2 * n + 1),
        PowerSeries.coeff (R := ℚ) k f * (mobiusTracePolynomial k).coeff n := by
  let s : PowerSeries ℚ := ∑ k ∈ Finset.range (2 * n + 1),
    PowerSeries.coeff (R := ℚ) k f • (PowerSeries.X : PowerSeries ℚ) ^ k
  have hcoeff (k : ℕ) (hk : k ≤ 2 * n) :
      PowerSeries.coeff (R := ℚ) k s = PowerSeries.coeff (R := ℚ) k f := by
    simp only [s, map_sum, map_smul, PowerSeries.coeff_X_pow, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      simp [Ne.symm hjk]
    · simp [Finset.mem_range, Nat.lt_succ_iff, hk]
  have hsum (t : Finset ℕ) :
      symmetrizedDescent (∑ k ∈ t, PowerSeries.coeff (R := ℚ) k f • (PowerSeries.X : PowerSeries ℚ) ^ k) =
        ∑ k ∈ t, PowerSeries.coeff (R := ℚ) k f • (mobiusTracePolynomial k : PowerSeries ℚ) := by
    induction t using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      simpa using symmetrizedDescent_smul 0 (0 : PowerSeries ℚ)
    | @insert k t hk ih =>
      rw [Finset.sum_insert hk, Finset.sum_insert hk, symmetrizedDescent_add,
        symmetrizedDescent_smul, symmetrizedDescent_X_pow, ih]
  rw [← coeff_symmetrizedDescent_congr n hcoeff]
  change PowerSeries.coeff (R := ℚ) n (symmetrizedDescent
    (∑ k ∈ Finset.range (2 * n + 1), PowerSeries.coeff (R := ℚ) k f •
      (PowerSeries.X : PowerSeries ℚ) ^ k)) = _
  rw [hsum]
  simp

end DirichletL
