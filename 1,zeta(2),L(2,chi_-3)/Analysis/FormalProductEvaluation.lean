import Analysis.FormalProductBounds
import Analysis.PowerSeriesEvaluation

/-!
Convergent evaluation of coefficient-stabilized products, used for the theta
identities in CDT v2 Section 11.1 and Lau-Lee-Ono v3 Theorem 4.1.4.
The summable majorant and normalization are recorded in
-/

namespace DirichletL

open Filter
open scoped Topology

private theorem coeff_mul_eq_left_of_X_pow_dvd_sub_one {R : Type*} [CommRing R]
    {g : PowerSeries R} {n : ℕ} (hg : PowerSeries.X ^ (n + 1) ∣ g - 1)
    (f : PowerSeries R) : PowerSeries.coeff (R := R) n (f * g) = PowerSeries.coeff (R := R) n f := by
  have h := PowerSeries.X_pow_dvd_iff.mp (dvd_mul_of_dvd_right hg f) n (by omega)
  simpa only [mul_sub, mul_one, map_sub, sub_eq_zero] using h

theorem formalProduct_eq_mul_tail {R : Type*} [CommRing R] {f : ℕ → PowerSeries R}
    (hf : ∀ i, PowerSeries.X ^ (i + 1) ∣ f (i + 1) - 1) :
    formalProduct f = f 0 * formalProduct (fun i => f (i + 1)) := by
  ext n
  calc
    PowerSeries.coeff (R := R) n (formalProduct f) =
        PowerSeries.coeff (R := R) n (∏ i ∈ Finset.range (n + 1), f i) := by
      rw [coeff_formalProduct, formalProductCoeff]
    _ = PowerSeries.coeff (R := R) n (∏ i ∈ Finset.range (n + 1 + 1), f i) := by
      rw [Finset.prod_range_succ _ (n + 1)]
      exact (coeff_mul_eq_left_of_X_pow_dvd_sub_one (hf n) _).symm
    _ = PowerSeries.coeff (R := R) n (f 0 * ∏ i ∈ Finset.range (n + 1), f (i + 1)) := by
      rw [Finset.prod_range_succ', mul_comm]
    _ = PowerSeries.coeff (R := R) n (f 0 * formalProduct (fun i => f (i + 1))) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [coeff_formalProduct_stable hf (Finset.antidiagonal.snd_le hp),
        coeff_formalProduct]

theorem hasSum_map_int_prod {ι : Type*} (s : Finset ι)
    {f : ι → PowerSeries ℤ} {g : ι → ℂ} {z : ℂ}
    (hs : ∀ i ∈ s, HasSum (fun n =>
      (PowerSeries.coeff (R := ℚ) n (PowerSeries.map (Int.castRingHom ℚ) (f i)) : ℂ) * z ^ n)
      (g i)) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) (∏ i ∈ s, f i)) : ℂ) * z ^ n)
      (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    convert hasSum_ite_eq (0 : ℕ) (1 : ℂ) using 1
    · ext n
      by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, map_mul]
    exact hasSum_powerSeries_mul (hs i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hs j (Finset.mem_insert_of_mem hj)))

private theorem norm_int_coeff_mul_pow_le {a : ℤ} {n : ℕ} (ha : |a| ≤ 4 ^ n) (z : ℂ) :
    ‖(a : ℂ) * z ^ n‖ ≤ (4 * ‖z‖) ^ n := by
  rw [norm_mul, norm_pow, mul_pow]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
  rw [Complex.norm_intCast]
  exact_mod_cast ha

theorem hasSum_formalProduct_of_hasProd {f : ℕ → PowerSeries ℤ} {g : ℕ → ℂ}
    {z a : ℂ} (hf : ∀ i, PowerSeries.X ^ (i + 1) ∣ f i - 1)
    (hc : ∀ i n, |PowerSeries.coeff (R := ℤ) n (f i)| ≤ 1) (hz : ‖z‖ < 1 / 4)
    (hs : ∀ i, HasSum (fun n =>
      (PowerSeries.coeff (R := ℚ) n (PowerSeries.map (Int.castRingHom ℚ) (f i)) : ℂ) * z ^ n)
      (g i)) (hg : HasProd g a) :
    HasSum (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) (formalProduct f)) : ℂ) * z ^ n) a := by
  have hgeom : Summable (fun n : ℕ => (4 * ‖z‖) ^ n) :=
    summable_geometric_of_lt_one (by positivity) (by linarith)
  have hbound (N n : ℕ) : ‖(PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) (∏ i ∈ Finset.range N, f i)) : ℂ) * z ^ n‖ ≤
      (4 * ‖z‖) ^ n := by
    simpa only [PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast] using
      norm_int_coeff_mul_pow_le (abs_coeff_prod_range_le_four_pow hf hc N n) z
  have hsum : Summable (fun n => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) (formalProduct f)) : ℂ) * z ^ n) := by
    apply hgeom.of_norm_bounded
    intro n
    simpa only [PowerSeries.coeff_map, Int.coe_castRingHom, Rat.cast_intCast] using
      norm_int_coeff_mul_pow_le (abs_coeff_formalProduct_le_four_pow hc n) z
  have hlim (n : ℕ) : Tendsto (fun N => (PowerSeries.coeff (R := ℚ) n
      (PowerSeries.map (Int.castRingHom ℚ) (∏ i ∈ Finset.range N, f i)) : ℂ) * z ^ n)
      atTop (𝓝 ((PowerSeries.coeff (R := ℚ) n
        (PowerSeries.map (Int.castRingHom ℚ) (formalProduct f)) : ℂ) * z ^ n)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    simp only [PowerSeries.coeff_map, Int.coe_castRingHom,
      coeff_formalProduct_stable hf (by omega : n ≤ M), coeff_formalProduct]
  have ht := tendsto_tsum_of_dominated_convergence hgeom hlim
    (Eventually.of_forall hbound)
  have he (N : ℕ) := (hasSum_map_int_prod (Finset.range N) (fun i _ => hs i)).tsum_eq
  simp_rw [he] at ht
  exact tendsto_nhds_unique hg.tendsto_prod_nat ht ▸ hsum.hasSum

end DirichletL
