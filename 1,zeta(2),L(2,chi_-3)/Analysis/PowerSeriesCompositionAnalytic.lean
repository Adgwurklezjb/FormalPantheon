import Analysis.PowerSeriesEvaluation
import Arithmetic.PowerSeriesDenominators

/-!
Compatibility of scalar analytic composition with rational formal powers,
used for the coordinate reversion in CDT v2, Section 11.1, equation `invert`.
-/

namespace DirichletL

open Filter
open scoped Topology NNReal ENNReal

theorem hasFPowerSeriesAt_of_eventually_hasSum {p : PowerSeries ℚ} {f : ℂ → ℂ}
    (h : ∀ᶠ z : ℂ in 𝓝 0,
      HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) (f z)) :
    HasFPowerSeriesAt f (complexSeries p) 0 := by
  have hr := pos_radius_complexSeries_of_eventually_hasSum h
  apply ((complexSeries p).hasFPowerSeriesOnBall hr).hasFPowerSeriesAt.congr
  filter_upwards [h] with z hz
  exact sum_complexSeries_eq_of_hasSum hz

theorem hasSum_powerSeries_pow {p : PowerSeries ℚ} {z a : ℂ}
    (hp : HasSum (fun n => (PowerSeries.coeff (R := ℚ) n p : ℂ) * z ^ n) a) (k : ℕ) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n (p ^ k) : ℂ) * z ^ n) (a ^ k) := by
  induction k with
  | zero =>
    change HasSum (fun n => (PowerSeries.coeff (R := ℚ) n 1 : ℂ) * z ^ n) 1
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℂ)) using 1
    funext n
    rw [PowerSeries.coeff_one]
    by_cases hn : n = 0
    · subst n
      simp only [if_pos rfl, ite_true, Rat.cast_one, pow_zero, mul_one]
    · simp only [if_neg hn, Rat.cast_zero, zero_mul]
  | succ k ih => simpa only [pow_succ] using hasSum_powerSeries_mul ih hp

theorem hasFPowerSeriesAt_powerSeries_pow {p : PowerSeries ℚ} {f : ℂ → ℂ}
    (hp : HasFPowerSeriesAt f (complexSeries p) 0) (k : ℕ) :
    HasFPowerSeriesAt (fun z => f z ^ k) (complexSeries (p ^ k)) 0 := by
  apply hasFPowerSeriesAt_of_eventually_hasSum
  filter_upwards [eventually_hasSum_of_hasFPowerSeriesAt hp] with z hz
  exact hasSum_powerSeries_pow hz k

theorem hasFPowerSeriesAt_powerSeries_mul {p q : PowerSeries ℚ} {f g : ℂ → ℂ}
    (hp : HasFPowerSeriesAt f (complexSeries p) 0)
    (hq : HasFPowerSeriesAt g (complexSeries q) 0) :
    HasFPowerSeriesAt (fun z => f z * g z) (complexSeries (p * q)) 0 := by
  apply hasFPowerSeriesAt_of_eventually_hasSum
  filter_upwards [eventually_hasSum_of_hasFPowerSeriesAt hp,
    eventually_hasSum_of_hasFPowerSeriesAt hq] with z hz h'z
  exact hasSum_powerSeries_mul hz h'z

theorem hasFPowerSeriesAt_complexSeries_X :
    HasFPowerSeriesAt (id : ℂ → ℂ) (complexSeries PowerSeries.X) 0 := by
  apply hasFPowerSeriesAt_of_eventually_hasSum
  apply Filter.Eventually.of_forall
  intro z
  convert (hasSum_ite_eq (1 : ℕ) z) using 1
  funext n
  rw [PowerSeries.coeff_X]
  by_cases hn : n = 1
  · subst n
    simp only [if_pos rfl, ite_true, Rat.cast_one, pow_one, one_mul]
  · simp only [if_neg hn, Rat.cast_zero, zero_mul]

theorem coeff_comp_eq_sum_monomial (q p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (q.comp p).coeff n = ∑ k ∈ Finset.range (n + 1), q.coeff k *
      ((complexSeries (PowerSeries.X ^ k)).comp p).coeff n := by
  classical
  have hc (a : FormalMultilinearSeries ℂ ℂ ℂ) :
      (a.comp p).coeff n = ∑ c : Composition n,
        a.coeff c.length * ∏ i : Fin c.length, p.coeff (c.blocksFun i) := by
    simp only [FormalMultilinearSeries.coeff, FormalMultilinearSeries.comp,
      ContinuousMultilinearMap.sum_apply, FormalMultilinearSeries.compAlongComposition_apply]
    apply Finset.sum_congr rfl
    intro c hc
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    change (∏ i : Fin c.length, p.coeff (c.blocksFun i)) * a.coeff c.length =
      a.coeff c.length * ∏ i : Fin c.length, p.coeff (c.blocksFun i)
    exact mul_comm _ _
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_eq_single c.length]
  · simp [coeff_complexSeries, PowerSeries.coeff_X_pow]
  · intro k hk hkn
    simp [coeff_complexSeries, PowerSeries.coeff_X_pow, hkn, Ne.symm hkn]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le c.length_le))).elim

theorem coeff_comp_complexSeries {p : PowerSeries ℚ}
    (hp : 0 < (complexSeries p).radius) (hp0 : PowerSeries.constantCoeff (R := ℚ) p = 0)
    (q : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    (q.comp (complexSeries p)).coeff n = ∑ k ∈ Finset.range (n + 1),
      q.coeff k * (PowerSeries.coeff (R := ℚ) n (p ^ k) : ℂ) := by
  have hf := ((complexSeries p).hasFPowerSeriesOnBall hp).hasFPowerSeriesAt
  have hf0 : (complexSeries p).sum 0 = 0 := by
    have h := hf.coeff_zero (fun _ => 1)
    simpa [complexSeries, FormalMultilinearSeries.ofScalars,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hp0] using h.symm
  rw [coeff_comp_eq_sum_monomial]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hm := hasFPowerSeriesAt_powerSeries_pow hasFPowerSeriesAt_complexSeries_X k
  have hm' : HasFPowerSeriesAt (fun z : ℂ => z ^ k)
      (complexSeries (PowerSeries.X ^ k)) ((complexSeries p).sum 0) := by
    simpa only [hf0, id_eq] using hm
  have he := (hm'.comp hf).eq_formalMultilinearSeries (hasFPowerSeriesAt_powerSeries_pow hf k)
  simpa only [coeff_complexSeries] using congrArg (fun s => s.coeff n) he

theorem complexSeries_subst {f g : PowerSeries ℚ}
    (hg : 0 < (complexSeries g).radius) (hg0 : PowerSeries.constantCoeff (R := ℚ) g = 0) :
    complexSeries (MvPowerSeries.subst (fun (_ : Unit) => g) f) =
      (complexSeries f).comp (complexSeries g) := by
  ext n v
  rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff]
  congr 1
  rw [coeff_complexSeries, coeff_subst_eq_sum f g hg0,
    Rat.cast_sum, coeff_comp_complexSeries hg hg0]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Rat.cast_mul, coeff_complexSeries]

theorem hasFPowerSeriesAt_powerSeries_subst {p q : PowerSeries ℚ} {f g : ℂ → ℂ}
    (hf : HasFPowerSeriesAt f (complexSeries p) 0)
    (hg : HasFPowerSeriesAt g (complexSeries q) 0)
    (hq0 : PowerSeries.constantCoeff (R := ℚ) q = 0) :
    HasFPowerSeriesAt (f ∘ g)
      (complexSeries (MvPowerSeries.subst (fun (_ : Unit) => q) p)) 0 := by
  have hg0 : g 0 = 0 := by
    have h := hg.coeff_zero (fun _ => 1)
    simpa [complexSeries, FormalMultilinearSeries.ofScalars,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hq0] using h.symm
  rw [complexSeries_subst hg.radius_pos hq0]
  exact (hg0.symm ▸ hf).comp hg

end DirichletL
