import Arithmetic.PowerSeriesDenominators

/-!
Formal inversion over the original coefficient ring for coordinates beginning
with `X`. This justifies the integral inversion step in CDT v2, Section 11.1,
equation `invert` (supplied `L2chi.tex` lines 7633-7637).
-/

namespace DirichletL

variable {R : Type*} [CommRing R]

/-- The triangular coefficient recursion for a normalized compositional inverse. -/
noncomputable def reversionCoeff (f : PowerSeries R) (n : ℕ) : R :=
  (if n = 1 then 1 else 0) -
    ∑ k : Fin n, reversionCoeff f k * PowerSeries.coeff (R := R) n (f ^ (k : ℕ))
termination_by n
decreasing_by exact k.isLt

theorem reversionCoeff_eq (f : PowerSeries R) (n : ℕ) :
    reversionCoeff f n = (if n = 1 then 1 else 0) -
      ∑ k ∈ Finset.range n, reversionCoeff f k * PowerSeries.coeff (R := R) n (f ^ k) := by
  conv_lhs => rw [reversionCoeff]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => reversionCoeff f k * PowerSeries.coeff (R := R) n (f ^ k)) n]

/-- The formal inverse candidate, with coefficients in the same ring as `f`. -/
noncomputable def reversion (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk (reversionCoeff f)

theorem coeff_reversion (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (R := R) n (reversion f) = reversionCoeff f n := by
  rw [reversion, PowerSeries.coeff_mk]

theorem map_reversion {S : Type*} [CommRing S] (F : R →+* S) (f : PowerSeries R) :
    PowerSeries.map F (reversion f) = reversion (PowerSeries.map F f) := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_map, coeff_reversion, coeff_reversion]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [reversionCoeff_eq, reversionCoeff_eq]
    simp only [map_sub, map_sum, map_mul, apply_ite, map_one, map_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [ih k (Finset.mem_range.mp hk)]
    simp only [← map_pow, PowerSeries.coeff_map]

theorem constantCoeff_reversion (f : PowerSeries R) :
    PowerSeries.constantCoeff (R := R) (reversion f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_reversion, reversionCoeff_eq]
  simp

theorem coeff_one_reversion (f : PowerSeries R) :
    PowerSeries.coeff (R := R) 1 (reversion f) = 1 := by
  rw [coeff_reversion, reversionCoeff_eq]
  simp [reversionCoeff_eq f 0]

/-- The diagonal coefficient in substitution by a zero-constant series. -/
theorem coeff_pow_self_of_constantCoeff_zero (f : PowerSeries R)
    (hf : PowerSeries.constantCoeff (R := R) f = 0) (n : ℕ) :
    PowerSeries.coeff (R := R) n (f ^ n) = (PowerSeries.coeff (R := R) 1 f) ^ n := by
  obtain ⟨u, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  have h1 : PowerSeries.coeff (R := R) 1 (PowerSeries.X * u) =
      PowerSeries.constantCoeff (R := R) u := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      PowerSeries.coeff_succ_X_mul 0 u
  rw [h1, mul_pow]
  simpa only [Nat.zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow] using
    PowerSeries.coeff_X_pow_mul (u ^ n) n 0

/-- Substitution by a coordinate beginning with `X` is injective. -/
theorem subst_injective_of_coeff_one (f : PowerSeries R)
    (hf0 : PowerSeries.constantCoeff (R := R) f = 0) (hf1 : PowerSeries.coeff (R := R) 1 f = 1) :
    Function.Injective (MvPowerSeries.subst (fun (_ : Unit) => f) :
      PowerSeries R → PowerSeries R) := by
  intro g h heq
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrArg (PowerSeries.coeff (R := R) n) heq
    rw [coeff_subst_eq_sum g f hf0, coeff_subst_eq_sum h f hf0] at hn
    simp only [Finset.sum_range_succ, coeff_pow_self_of_constantCoeff_zero f hf0,
      hf1, one_pow, mul_one] at hn
    have hsum :
        (∑ k ∈ Finset.range n, PowerSeries.coeff (R := R) k g * PowerSeries.coeff (R := R) n (f ^ k)) =
        ∑ k ∈ Finset.range n, PowerSeries.coeff (R := R) k h * PowerSeries.coeff (R := R) n (f ^ k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k (Finset.mem_range.mp hk)]
    rw [hsum] at hn
    exact add_left_cancel hn

/-- The recursively constructed inverse composed with the original coordinate. -/
theorem subst_reversion (f : PowerSeries R)
    (hf0 : PowerSeries.constantCoeff (R := R) f = 0) (hf1 : PowerSeries.coeff (R := R) 1 f = 1) :
    MvPowerSeries.subst (fun (_ : Unit) => f) (reversion f) = PowerSeries.X := by
  apply PowerSeries.ext
  intro n
  rw [coeff_subst_eq_sum _ f hf0, PowerSeries.coeff_X]
  simp only [Finset.sum_range_succ, coeff_reversion,
    coeff_pow_self_of_constantCoeff_zero f hf0, hf1, one_pow, mul_one]
  rw [reversionCoeff_eq f n]
  ring

/-- The original coordinate composed with its recursively constructed inverse. -/
theorem reversion_subst (f : PowerSeries R)
    (hf0 : PowerSeries.constantCoeff (R := R) f = 0) (hf1 : PowerSeries.coeff (R := R) 1 f = 1) :
    MvPowerSeries.subst (fun (_ : Unit) => reversion f) f = PowerSeries.X := by
  apply subst_injective_of_coeff_one f hf0 hf1
  have hs : MvPowerSeries.HasSubst (fun (_ : Unit) => f) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hf0)
  have ht : MvPowerSeries.HasSubst (fun (_ : Unit) => reversion f) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_reversion f)
  rw [MvPowerSeries.subst_comp_subst_apply ht hs, subst_reversion f hf0 hf1]
  calc
    MvPowerSeries.subst (fun (_ : Unit) => (PowerSeries.X : PowerSeries R)) f = f := by
      convert congrFun (MvPowerSeries.subst_self (σ := Unit) (R := R)) f using 1
    _ = MvPowerSeries.subst (fun (_ : Unit) => f) PowerSeries.X :=
      (MvPowerSeries.subst_X hs ()).symm

/-- The integral formal inversion assertion used in CDT equation `invert`. -/
theorem exists_integral_subst_inverse (f : PowerSeries ℤ)
    (hf0 : PowerSeries.constantCoeff (R := ℤ) f = 0) (hf1 : PowerSeries.coeff (R := ℤ) 1 f = 1) :
    ∃ g : PowerSeries ℤ, PowerSeries.constantCoeff (R := ℤ) g = 0 ∧
      PowerSeries.coeff (R := ℤ) 1 g = 1 ∧
      MvPowerSeries.subst (fun (_ : Unit) => f) g = PowerSeries.X ∧
      MvPowerSeries.subst (fun (_ : Unit) => g) f = PowerSeries.X := by
  exact ⟨reversion f, constantCoeff_reversion f, coeff_one_reversion f,
    subst_reversion f hf0 hf1, reversion_subst f hf0 hf1⟩

end DirichletL
