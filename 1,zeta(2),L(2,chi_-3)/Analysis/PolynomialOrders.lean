import Mathlib

/-!
Polynomial evaluation and meromorphic order for the local-to-global step
in CDT v2, proof of Lemma `14functions`, immediately before equation `b3eq`.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

theorem order_polynomial_eval {p : ℂ[X]} (hp : p ≠ 0) (a : ℂ)
    (h : MeromorphicAt (fun z => p.eval z) a) :
    meromorphicOrderAt (fun z => p.eval z) a = ((p.rootMultiplicity a : ℤ) : WithTop ℤ) := by
  let g := p /ₘ (X - C a) ^ p.rootMultiplicity a
  apply (meromorphicOrderAt_eq_int_iff h).mpr
  refine ⟨fun z => g.eval z,
    (AnalyticOnNhd.eval_polynomial g) a (Set.mem_univ a),
    eval_divByMonic_pow_rootMultiplicity_ne_zero a hp, ?_⟩
  apply Eventually.of_forall
  intro z
  have he := congrArg (Polynomial.eval z) (pow_mul_divByMonic_rootMultiplicity_eq p a)
  simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul, zpow_natCast]
    using he.symm

theorem eventually_ne_zero_polynomial_eval {p : ℂ[X]} (hp : p ≠ 0) (a : ℂ) :
    ∀ᶠ z in 𝓝[≠] a, p.eval z ≠ 0 := by
  let g := p /ₘ (X - C a) ^ p.rootMultiplicity a
  have hg : g.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
  have hgne := g.continuous.continuousAt.eventually_ne hg
  filter_upwards [hgne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hgz hza
  have he := congrArg (Polynomial.eval z) (pow_mul_divByMonic_rootMultiplicity_eq p a)
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at he
  rw [← he]
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hza)) hgz

theorem order_polynomial_div {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0) (a : ℂ) :
    meromorphicOrderAt (fun z => p.eval z / q.eval z) a =
      (((p.rootMultiplicity a : ℤ) - q.rootMultiplicity a : ℤ) : WithTop ℤ) := by
  let hp' := ((AnalyticOnNhd.eval_polynomial p) a (Set.mem_univ a)).meromorphicAt
  let hq' := ((AnalyticOnNhd.eval_polynomial q) a (Set.mem_univ a)).meromorphicAt
  have he : (fun z => p.eval z / q.eval z) =ᶠ[𝓝[≠] a]
      (fun z => p.eval z) * (fun z => q.eval z)⁻¹ := by
    filter_upwards [] with z using div_eq_mul_inv _ _
  rw [meromorphicOrderAt_congr he]
  rw [meromorphicOrderAt_mul hp' hq'.inv, meromorphicOrderAt_inv,
    order_polynomial_eval hp a hp', order_polynomial_eval hq a hq']
  simp [sub_eq_add_neg]

theorem eval_inv_eq_reflect (p : ℂ[X]) (n : ℕ) (hp : p.natDegree ≤ n)
    {z : ℂ} (hz : z ≠ 0) : p.eval z⁻¹ = (p.reflect n).eval z * (z⁻¹) ^ n := by
  letI := invertibleOfNonzero (inv_ne_zero hz)
  simpa using (eval₂_reflect_mul_pow (RingHom.id ℂ) z⁻¹ n p hp).symm

theorem meromorphicAt_polynomial_eval_inv (p : ℂ[X]) :
    MeromorphicAt (fun z => p.eval z⁻¹) 0 := by
  have hp := ((AnalyticOnNhd.eval_polynomial p.reverse) 0 (Set.mem_univ 0)).meromorphicAt
  have hpow : AnalyticAt ℂ (fun z : ℂ => z ^ p.natDegree) 0 := analyticAt_id.pow _
  apply (hp.div hpow.meromorphicAt).congr
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [eval_inv_eq_reflect p p.natDegree le_rfl hz]
  simp [reverse, div_eq_mul_inv, inv_pow]

theorem order_polynomial_eval_inv {p : ℂ[X]} (hp : p ≠ 0)
    (h : MeromorphicAt (fun z => p.eval z⁻¹) 0) :
    meromorphicOrderAt (fun z => p.eval z⁻¹) 0 = ((-(p.natDegree : ℤ) : ℤ) : WithTop ℤ) := by
  apply (meromorphicOrderAt_eq_int_iff h).mpr
  refine ⟨fun z => p.reverse.eval z,
    (AnalyticOnNhd.eval_polynomial p.reverse) 0 (Set.mem_univ 0), ?_, ?_⟩
  · simpa [← coeff_zero_eq_eval_zero] using leadingCoeff_ne_zero.mpr hp
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [eval_inv_eq_reflect p p.natDegree le_rfl hz]
    simp [reverse, smul_eq_mul, zpow_neg, inv_pow, mul_comm]

theorem order_polynomial_div_inv {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    meromorphicOrderAt (fun z => p.eval z⁻¹ / q.eval z⁻¹) 0 =
      (((q.natDegree : ℤ) - p.natDegree : ℤ) : WithTop ℤ) := by
  have he : (fun z => p.eval z⁻¹ / q.eval z⁻¹) =ᶠ[𝓝[≠] 0]
      (fun z => p.eval z⁻¹) * (fun z => q.eval z⁻¹)⁻¹ := by
    filter_upwards [] with z using div_eq_mul_inv _ _
  rw [meromorphicOrderAt_congr he]
  rw [meromorphicOrderAt_mul (meromorphicAt_polynomial_eval_inv p)
      (meromorphicAt_polynomial_eval_inv q).inv, meromorphicOrderAt_inv,
    order_polynomial_eval_inv hp (meromorphicAt_polynomial_eval_inv p),
    order_polynomial_eval_inv hq (meromorphicAt_polynomial_eval_inv q)]
  simp [sub_eq_add_neg, add_comm]

theorem eventually_ne_zero_polynomial_eval_inv {p : ℂ[X]} (hp : p ≠ 0) :
    ∀ᶠ z : ℂ in 𝓝[≠] 0, p.eval z⁻¹ ≠ 0 := by
  have hrev : p.reverse.eval 0 ≠ 0 := by
    simpa [← coeff_zero_eq_eval_zero] using leadingCoeff_ne_zero.mpr hp
  have hne := p.reverse.continuous.continuousAt.eventually_ne hrev
  filter_upwards [hne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hrevz hz
  rw [eval_inv_eq_reflect p p.natDegree le_rfl hz]
  exact mul_ne_zero hrevz (pow_ne_zero _ (inv_ne_zero hz))

end DirichletL
