import Mathlib

/-!
Holomorphy and nonvanishing of the complex products underlying the theta
identities, Lau-Lee-Ono v3 Theorem 1.1.1 and CDT v2 Section 11.1.
Principal logarithms are used only for factors in the open disk about 1
-/

namespace DirichletL

open Filter
open scoped Topology

private theorem norm_mul_pow_le_geometric {s q : ℂ} {r : ℝ} {k i : ℕ}
    (hs : ‖s‖ ≤ 1) (hq : ‖q‖ ≤ r) (hr : r ≤ 1) (hk : i + 1 ≤ k) :
    ‖s * q ^ k‖ ≤ r ^ (i + 1) := by
  have hr0 : 0 ≤ r := (norm_nonneg q).trans hq
  calc
    ‖s * q ^ k‖ = ‖s‖ * ‖q‖ ^ k := by rw [norm_mul, norm_pow]
    _ ≤ 1 * r ^ k := mul_le_mul hs (pow_le_pow_left₀ (norm_nonneg _) hq _)
      (pow_nonneg (norm_nonneg _) _) zero_le_one
    _ ≤ r ^ (i + 1) := by
      rw [one_mul]
      exact pow_le_pow_of_le_one hr0 hr hk

private theorem summable_mul_pow {s q : ℂ} {e : ℕ → ℕ}
    (hs : ‖s‖ ≤ 1) (he : ∀ i, i + 1 ≤ e i) (hq : ‖q‖ < 1) :
    Summable (fun i => s * q ^ e i) := by
  have hgeom : Summable (fun i : ℕ => ‖q‖ ^ (i + 1)) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right ‖q‖
  exact hgeom.of_norm_bounded (fun i => norm_mul_pow_le_geometric hs le_rfl hq.le (he i))

private theorem one_add_mul_pow_mem_slitPlane {s q : ℂ} {e : ℕ → ℕ}
    (hs : ‖s‖ ≤ 1) (he : ∀ i, i + 1 ≤ e i) (hq : ‖q‖ < 1) (i : ℕ) :
    1 + s * q ^ e i ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_of_norm_lt_one
  calc
    ‖s * q ^ e i‖ ≤ ‖q‖ ^ (i + 1) := norm_mul_pow_le_geometric hs le_rfl hq.le (he i)
    _ ≤ ‖q‖ := by
      simpa using pow_le_pow_of_le_one (norm_nonneg q) hq.le (by omega : 1 ≤ i + 1)
    _ < 1 := hq

theorem multipliable_one_add_mul_pow {s q : ℂ} {e : ℕ → ℕ}
    (hs : ‖s‖ ≤ 1) (he : ∀ i, i + 1 ≤ e i) (hq : ‖q‖ < 1) :
    Multipliable (fun i => 1 + s * q ^ e i) :=
  Complex.multipliable_one_add_of_summable (summable_mul_pow hs he hq)

theorem tprod_one_add_mul_pow_ne_zero {s q : ℂ} {e : ℕ → ℕ}
    (hs : ‖s‖ ≤ 1) (he : ∀ i, i + 1 ≤ e i) (hq : ‖q‖ < 1) :
    (∏' i, (1 + s * q ^ e i)) ≠ 0 := by
  rw [← Complex.cexp_tsum_eq_tprod
    (fun i => Complex.slitPlane_ne_zero (one_add_mul_pow_mem_slitPlane hs he hq i))
    (Complex.summable_log_one_add_of_summable (summable_mul_pow hs he hq))]
  exact Complex.exp_ne_zero _

theorem differentiableOn_tprod_one_add_mul_pow {s : ℂ} {e : ℕ → ℕ}
    (hs : ‖s‖ ≤ 1) (he : ∀ i, i + 1 ≤ e i) :
    DifferentiableOn ℂ (fun q => ∏' i, (1 + s * q ^ e i)) (Metric.ball 0 1) := by
  intro q hq
  have hq1 : ‖q‖ < 1 := by simpa using hq
  obtain ⟨r, hqr, hr⟩ := exists_between hq1
  have hr0 : 0 ≤ r := (norm_nonneg q).trans hqr.le
  have hgeom : Summable (fun i : ℕ => r ^ (i + 1)) := by
    simpa only [pow_succ] using (summable_geometric_of_lt_one hr0 hr).mul_right r
  have hu := hgeom.tendstoUniformlyOn_tsum_nat_log_one_add (K := Metric.ball (0 : ℂ) r)
    (f := fun i w => s * w ^ e i) (Eventually.of_forall (fun i w hw =>
      norm_mul_pow_le_geometric hs (by simpa using (Metric.mem_ball.mp hw).le) hr.le (he i)))
  have hd : DifferentiableOn ℂ (fun w => ∑' i, Complex.log (1 + s * w ^ e i))
      (Metric.ball 0 r) := by
    apply hu.tendstoLocallyUniformlyOn.differentiableOn _ Metric.isOpen_ball
    apply Eventually.of_forall
    intro N
    apply DifferentiableOn.fun_sum
    intro i _
    apply ((differentiableOn_const 1).add ((differentiableOn_const s).mul
      (differentiableOn_id.pow (e i)))).clog
    intro w hw
    exact one_add_mul_pow_mem_slitPlane hs he ((by simpa using hw : ‖w‖ < r).trans hr) i
  have hp : DifferentiableOn ℂ (fun w => ∏' i, (1 + s * w ^ e i)) (Metric.ball 0 r) := by
    apply hd.cexp.congr
    intro w hw
    have hw1 : ‖w‖ < 1 := (by simpa using hw : ‖w‖ < r).trans hr
    exact (Complex.cexp_tsum_eq_tprod
      (fun i => Complex.slitPlane_ne_zero (one_add_mul_pow_mem_slitPlane hs he hw1 i))
      (Complex.summable_log_one_add_of_summable (summable_mul_pow hs he hw1))).symm
  exact (hp.differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hqr))).differentiableWithinAt

end DirichletL
