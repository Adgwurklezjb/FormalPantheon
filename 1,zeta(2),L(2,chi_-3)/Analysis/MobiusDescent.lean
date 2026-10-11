import Analysis.Symmetrization
import Arithmetic.PowerSeriesSubstitutionDerivative

/-!
Formal descent through `y = x + x/(x-1)` in CDT v2, Lemma `etalecover`
and Definition `defG`. The construction uses the unit leading coefficient
of the order-two coordinate. No analytic continuation is asserted.
-/

namespace DirichletL

private theorem X_sq_dvd_mobiusCoordinateQ :
    (PowerSeries.X : PowerSeries ℚ) ^ 2 ∣ mobiusCoordinateQ := by
  refine ⟨-PowerSeries.map (Int.castRingHom ℚ) (oneSubInv 1), ?_⟩
  rw [mobiusCoordinateQ_eq]
  ring

private theorem coeff_mobiusCoordinateQ_pow_of_lt {n k : ℕ} (hn : n < 2 * k) :
    PowerSeries.coeff (R := ℚ) n (mobiusCoordinateQ ^ k) = 0 := by
  apply PowerSeries.X_pow_dvd_iff.mp _ n hn
  rw [pow_mul]
  exact pow_dvd_pow_of_dvd X_sq_dvd_mobiusCoordinateQ k

private theorem coeff_mobiusCoordinateQ_pow (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ n) = (-1 : ℚ) ^ n := by
  obtain ⟨u, hu⟩ := X_sq_dvd_mobiusCoordinateQ
  have hu0 : PowerSeries.constantCoeff (R := ℚ) u = -1 := by
    have h := coeff_two_mobiusCoordinateQ
    rw [hu] at h
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (PowerSeries.coeff_X_pow_mul u 2 0).symm.trans h
  rw [hu, mul_pow, ← pow_mul]
  simpa only [Nat.zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow, hu0] using PowerSeries.coeff_X_pow_mul (u ^ n) (2 * n) 0

private theorem coeff_even_subst_mobiusCoordinateQ (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (2 * n)
        (MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) f) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff (R := ℚ) k f *
        PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k) := by
  rw [coeff_subst_eq_sum f _ constantCoeff_mobiusCoordinateQ]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro k hk hkn
  have hnk : n < k := by simpa using hkn
  rw [coeff_mobiusCoordinateQ_pow_of_lt (by omega), mul_zero]

private theorem eq_zero_of_mobiusInvariant_of_even_coeff_zero (f : PowerSeries ℚ)
    (hf : MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f = f)
    (heven : ∀ n : ℕ, PowerSeries.coeff (R := ℚ) (2 * n) f = 0) : f = 0 := by
  apply PowerSeries.ext
  intro n
  simp only [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with hn | hn
    · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hn
      exact heven k
    · have h := congrArg (PowerSeries.coeff (R := ℚ) n) hf
      rw [coeff_subst_eq_sum f _ constantCoeff_mobiusInvolutionQ,
        Finset.sum_eq_single n] at h
      · rw [coeff_pow_self_of_constantCoeff_zero _ constantCoeff_mobiusInvolutionQ,
          coeff_one_mobiusInvolutionQ, hn.neg_one_pow] at h
        linarith
      · intro k hk hkn
        rw [ih k (by have := Finset.mem_range.mp hk; omega), zero_mul]
      · simp

/-- Coefficients obtained by solving the even-degree pullback equations. -/
noncomputable def mobiusDescentCoeff (f : PowerSeries ℚ) (n : ℕ) : ℚ :=
  (-1) ^ n * (PowerSeries.coeff (R := ℚ) (2 * n) f -
    ∑ k : Fin n, mobiusDescentCoeff f k *
      PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ (k : ℕ)))
termination_by n
decreasing_by exact k.isLt

theorem mobiusDescentCoeff_eq (f : PowerSeries ℚ) (n : ℕ) :
    mobiusDescentCoeff f n = (-1) ^ n * (PowerSeries.coeff (R := ℚ) (2 * n) f -
      ∑ k ∈ Finset.range n, mobiusDescentCoeff f k *
        PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k)) := by
  conv_lhs => rw [mobiusDescentCoeff]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => mobiusDescentCoeff f k *
      PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k)) n]

/-- The formal series descending a Mobius-invariant rational series. -/
noncomputable def mobiusDescent (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (mobiusDescentCoeff f)

theorem coeff_mobiusDescent (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) n (mobiusDescent f) = mobiusDescentCoeff f n := by
  rw [mobiusDescent, PowerSeries.coeff_mk]

theorem coeff_even_subst_mobiusDescent (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff (R := ℚ) (2 * n)
        (MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) (mobiusDescent f)) =
      PowerSeries.coeff (R := ℚ) (2 * n) f := by
  rw [coeff_even_subst_mobiusCoordinateQ, Finset.sum_range_succ]
  simp only [coeff_mobiusDescent, coeff_mobiusCoordinateQ_pow]
  rw [mobiusDescentCoeff_eq f n]
  have hsign : (-1 : ℚ) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = (∑ k ∈ Finset.range n, mobiusDescentCoeff f k *
          PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k)) +
        ((-1 : ℚ) ^ n * (-1) ^ n) *
          (PowerSeries.coeff (R := ℚ) (2 * n) f -
            ∑ k ∈ Finset.range n, mobiusDescentCoeff f k *
              PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k)) := by ring
    _ = _ := by rw [hsign]; ring

private theorem subst_mobiusCoordinateQ_invariant (f : PowerSeries ℚ) :
    MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ)
        (MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) f) =
      MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) f := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusCoordinateQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusInvolutionQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  rw [MvPowerSeries.subst_comp_subst_apply hy hw]
  simp only [subst_mobiusCoordinateQ]

/-- The formal part of CDT Lemma `etalecover`: invariant series descend to `y`. -/
theorem subst_mobiusDescent (f : PowerSeries ℚ)
    (hf : MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f = f) :
    MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) (mobiusDescent f) = f := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mobiusInvariant_of_even_coeff_zero
  · have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusInvolutionQ) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
    rw [← MvPowerSeries.coe_substAlgHom hw, map_sub]
    simp only [MvPowerSeries.substAlgHom_apply, subst_mobiusCoordinateQ_invariant, hf]
  · intro n
    rw [map_sub, coeff_even_subst_mobiusDescent, sub_self]

theorem subst_mobiusCoordinateQ_injective :
    Function.Injective (MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) :
      PowerSeries ℚ → PowerSeries ℚ) := by
  intro f g hfg
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have h := congrArg (PowerSeries.coeff (R := ℚ) (2 * n)) hfg
    rw [coeff_even_subst_mobiusCoordinateQ, coeff_even_subst_mobiusCoordinateQ,
      Finset.sum_range_succ, Finset.sum_range_succ, coeff_mobiusCoordinateQ_pow] at h
    have hsum :
        (∑ k ∈ Finset.range n, PowerSeries.coeff (R := ℚ) k f *
          PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k)) =
        ∑ k ∈ Finset.range n, PowerSeries.coeff (R := ℚ) k g *
          PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k (Finset.mem_range.mp hk)]
    rw [hsum] at h
    exact mul_right_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℚ) ≠ 0))
      (add_left_cancel h)

theorem mobiusDescent_subst (f : PowerSeries ℚ) :
    mobiusDescent (MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) f) = f := by
  apply subst_mobiusCoordinateQ_injective
  exact subst_mobiusDescent _ (subst_mobiusCoordinateQ_invariant f)

theorem existsUnique_mobiusDescent (f : PowerSeries ℚ)
    (hf : MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f = f) :
    ∃! g : PowerSeries ℚ,
      MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) g = f := by
  refine ⟨mobiusDescent f, subst_mobiusDescent f hf, ?_⟩
  intro g hg
  exact subst_mobiusCoordinateQ_injective (hg.trans (subst_mobiusDescent f hf).symm)

theorem constantCoeff_mobiusDescent (f : PowerSeries ℚ) :
    PowerSeries.constantCoeff (R := ℚ) (mobiusDescent f) = PowerSeries.constantCoeff (R := ℚ) f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_mobiusDescent,
    mobiusDescentCoeff_eq]
  simp

theorem coeff_one_mobiusDescent (f : PowerSeries ℚ) :
    PowerSeries.coeff (R := ℚ) 1 (mobiusDescent f) = -PowerSeries.coeff (R := ℚ) 2 f := by
  rw [coeff_mobiusDescent, mobiusDescentCoeff_eq]
  simp [PowerSeries.coeff_one]

/-- CDT Definition `defG`, now represented as a series in the invariant coordinate. -/
noncomputable def symmetrizedDescent (f : PowerSeries ℚ) : PowerSeries ℚ :=
  mobiusDescent (symmetrizedFormal f)

theorem subst_symmetrizedDescent (f : PowerSeries ℚ) :
    MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) (symmetrizedDescent f) =
      symmetrizedFormal f := by
  exact subst_mobiusDescent _ (subst_mobiusInvolutionQ_symmetrizedFormal f)

/-- Differentiation of the trace identity in CDT `polysym`, without division at zero. -/
theorem subst_derivative_symmetrizedDescent (f : PowerSeries ℚ) :
    MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ)
        (symmetrizedDescent f).derivativeFun * mobiusCoordinateQ.derivativeFun =
      f.derivativeFun +
        MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f.derivativeFun *
          mobiusInvolutionQ.derivativeFun := by
  have h := congrArg PowerSeries.derivativeFun (subst_symmetrizedDescent f)
  change PowerSeries.derivativeFun
      (MvPowerSeries.subst (fun (_ : Unit) => mobiusCoordinateQ) (symmetrizedDescent f)) =
    PowerSeries.derivativeFun
      (f + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f) at h
  rwa [derivativeFun_subst _ _ constantCoeff_mobiusCoordinateQ,
    PowerSeries.derivativeFun_add,
    derivativeFun_subst _ _ constantCoeff_mobiusInvolutionQ] at h

theorem symmetrizedDescent_add (f g : PowerSeries ℚ) :
    symmetrizedDescent (f + g) = symmetrizedDescent f + symmetrizedDescent g := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusCoordinateQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusInvolutionQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  apply subst_mobiusCoordinateQ_injective
  rw [MvPowerSeries.subst_add hy, subst_symmetrizedDescent,
    subst_symmetrizedDescent, subst_symmetrizedDescent]
  change f + g + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) (f + g) =
    (f + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f) +
      (g + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) g)
  rw [MvPowerSeries.subst_add hw]
  abel

theorem symmetrizedDescent_smul (a : ℚ) (f : PowerSeries ℚ) :
    symmetrizedDescent (a • f) = a • symmetrizedDescent f := by
  have hy : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusCoordinateQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusCoordinateQ)
  have hw : MvPowerSeries.HasSubst (fun (_ : Unit) => mobiusInvolutionQ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_mobiusInvolutionQ)
  apply subst_mobiusCoordinateQ_injective
  rw [MvPowerSeries.subst_smul hy, subst_symmetrizedDescent, subst_symmetrizedDescent]
  change a • f + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) (a • f) =
    a • (f + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) f)
  rw [MvPowerSeries.subst_smul hw, smul_add]

theorem constantCoeff_symmetrizedDescent (f : PowerSeries ℚ) :
    PowerSeries.constantCoeff (R := ℚ) (symmetrizedDescent f) =
      2 * PowerSeries.constantCoeff (R := ℚ) f := by
  rw [symmetrizedDescent, constantCoeff_mobiusDescent, constantCoeff_symmetrizedFormal]

theorem coeff_one_symmetrizedDescent (f : PowerSeries ℚ) :
    PowerSeries.coeff (R := ℚ) 1 (symmetrizedDescent f) =
      PowerSeries.coeff (R := ℚ) 1 f - 2 * PowerSeries.coeff (R := ℚ) 2 f := by
  rw [symmetrizedDescent, coeff_one_mobiusDescent, coeff_two_symmetrizedFormal]
  ring

/-- The constant term of `G_A` in CDT Definition `defG`. -/
theorem constantCoeff_symmetrizedDescent_hA :
    PowerSeries.constantCoeff (R := ℚ) (symmetrizedDescent hA) = 2 := by
  rw [constantCoeff_symmetrizedDescent,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hA_coeff_zero]
  norm_num

/-- The first `y`-coefficient of `G_A` in CDT Definition `defG`. -/
theorem coeff_one_symmetrizedDescent_hA :
    PowerSeries.coeff (R := ℚ) 1 (symmetrizedDescent hA) = -27 := by
  rw [coeff_one_symmetrizedDescent, hA_coeff_one, hA_coeff_two]
  norm_num

private theorem coeff_mobiusCoordinateQ_pow_int (n k : ℕ) :
    PowerSeries.coeff (R := ℚ) n (mobiusCoordinateQ ^ k) =
      (PowerSeries.coeff (R := ℤ) n ((PowerSeries.X + mobiusInvolution) ^ k) : ℚ) := by
  have hy : mobiusCoordinateQ =
      PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.X + mobiusInvolution) := by
    simp [mobiusCoordinateQ, mobiusInvolutionQ]
  rw [hy, ← map_pow, PowerSeries.coeff_map]
  rfl

private theorem sqIntegral_mobiusDescent_of_dvd (f : PowerSeries ℚ) (D : ℕ → ℕ)
    (hD : ∀ k n : ℕ, k ≤ n → D k ∣ D n)
    (hf : ∀ n : ℕ, SqIntegral (PowerSeries.coeff (R := ℚ) (2 * n) f) (D n)) (n : ℕ) :
    SqIntegral (PowerSeries.coeff (R := ℚ) n (mobiusDescent f)) (D n) := by
  simp only [coeff_mobiusDescent]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [mobiusDescentCoeff_eq]
    have hsum : SqIntegral
        (∑ k ∈ Finset.range n, mobiusDescentCoeff f k *
          PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k)) (D n) := by
      apply SqIntegral.sum
      intro k hk
      rw [coeff_mobiusCoordinateQ_pow_int]
      exact ((ih k (Finset.mem_range.mp hk)).of_dvd
        (hD k n (Nat.le_of_lt (Finset.mem_range.mp hk)))).mul_intCast _
    have hdiff : SqIntegral
        (PowerSeries.coeff (R := ℚ) (2 * n) f -
          ∑ k ∈ Finset.range n, mobiusDescentCoeff f k *
            PowerSeries.coeff (R := ℚ) (2 * n) (mobiusCoordinateQ ^ k)) (D n) := by
      simpa [sub_eq_add_neg] using (hf n).add (hsum.mul_intCast (-1))
    simpa [mul_comm] using hdiff.mul_intCast ((-1 : ℤ) ^ n)

/-- Descent doubles the index in the squared prefix-lcm bound. -/
theorem sqIntegral_mobiusDescent {f : PowerSeries ℚ} (hf : LcmSqIntegral f) (n : ℕ) :
    SqIntegral (PowerSeries.coeff (R := ℚ) n (mobiusDescent f)) (lcmPrefix (2 * n)) := by
  apply sqIntegral_mobiusDescent_of_dvd f (fun k => lcmPrefix (2 * k))
  · intro k m hkm
    exact lcmPrefix_dvd (Nat.mul_le_mul_left 2 hkm)
  · intro k
    exact hf (2 * k)

/-- The exact denominator bound underlying CDT Lemma `Gdenominatortype`. -/
theorem sqIntegral_symmetrizedDescent {f : PowerSeries ℚ} (hf : LcmSqIntegral f)
    (n : ℕ) :
    SqIntegral (PowerSeries.coeff (R := ℚ) n (symmetrizedDescent f)) (lcmPrefix (2 * n)) := by
  exact sqIntegral_mobiusDescent (lcmSqIntegral_symmetrizedFormal hf) n

theorem sqIntegral_symmetrizedDescent_h_integer_combination (a b c : ℤ) (n : ℕ) :
    SqIntegral
      (PowerSeries.coeff (R := ℚ) n
        (symmetrizedDescent ((a : ℚ) • hA + (b : ℚ) • hB + (c : ℚ) • hC)))
      (lcmPrefix (2 * n)) := by
  exact sqIntegral_symmetrizedDescent (lcmSqIntegral_h_integer_combination a b c) n

theorem exists_int_coeff_symmetrizedDescent (f : PowerSeries ℤ) (n : ℕ) :
    ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n
      (symmetrizedDescent (PowerSeries.map (Int.castRingHom ℚ) f)) = z := by
  let fq := PowerSeries.map (Int.castRingHom ℚ) f
  have hf (k : ℕ) : SqIntegral (PowerSeries.coeff (R := ℚ) k fq) 1 := by
    refine ⟨PowerSeries.coeff (R := ℤ) k f, ?_⟩
    simp [fq, PowerSeries.coeff_map]
  have hs (k : ℕ) : SqIntegral
      (PowerSeries.coeff (R := ℚ) k
        (MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) fq)) 1 := by
    rw [coeff_subst_eq_sum fq _ constantCoeff_mobiusInvolutionQ]
    apply SqIntegral.sum
    intro j hj
    rw [mobiusInvolutionQ, ← map_pow, PowerSeries.coeff_map]
    exact (hf j).mul_intCast _
  have hsym (k : ℕ) : SqIntegral (PowerSeries.coeff (R := ℚ) k (symmetrizedFormal fq)) 1 := by
    change SqIntegral (PowerSeries.coeff (R := ℚ) k
      (fq + MvPowerSeries.subst (fun (_ : Unit) => mobiusInvolutionQ) fq)) 1
    rw [map_add]
    exact (hf k).add (hs k)
  have h := sqIntegral_mobiusDescent_of_dvd (symmetrizedFormal fq) (fun _ => 1)
    (fun _ _ _ => dvd_rfl) (fun k => hsym (2 * k)) n
  simpa [SqIntegral, symmetrizedDescent, fq] using h

/-- The integral `G_A` assertion in CDT Definition `defG`. -/
theorem exists_int_coeff_symmetrizedDescent_hA (n : ℕ) :
    ∃ z : ℤ, PowerSeries.coeff (R := ℚ) n (symmetrizedDescent hA) = z := by
  simpa only [map_zagierIntegerGenerating, hA] using
    exists_int_coeff_symmetrizedDescent zagierIntegerGenerating n

end DirichletL
