import Mathlib

/-!
Local analytic factorizations for the Frobenius calculation in CDT v2,
proof of Lemma `14functions`, between equations `remaining` and `b3eq`.
Integer exponents include poles; vanishing leading derivative factors are retained.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem eventuallyEq_deriv_of_punctured {f g : ℂ → ℂ} {a : ℂ}
    (h : f =ᶠ[𝓝[≠] a] g) : deriv f =ᶠ[𝓝[≠] a] deriv g := by
  have h' := eventually_eventually_nhdsWithin.mpr h
  filter_upwards [h', self_mem_nhdsWithin] with z hz hza
  rw [nhdsWithin_eq_nhds.mpr (isOpen_compl_singleton.mem_nhds hza)] at hz
  exact Filter.EventuallyEq.deriv_eq hz

theorem exists_analytic_factor_deriv {f g : ℂ → ℂ} {a : ℂ} (N : ℤ)
    (hg : AnalyticAt ℂ g a) (hf : f =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * g z) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧ u a = (N : ℂ) * g a ∧
      deriv f =ᶠ[𝓝[≠] a] fun z => (z - a) ^ (N - 1) * u z := by
  let u : ℂ → ℂ := fun z => (N : ℂ) * g z + (z - a) * deriv g z
  refine ⟨u, (analyticAt_const.mul hg).add ((analyticAt_id.sub analyticAt_const).mul hg.deriv),
    by simp [u], ?_⟩
  filter_upwards [eventuallyEq_deriv_of_punctured hf,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hgz hza
  have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hd := ((hasDerivAt_zpow N (z - a) (Or.inl hne)).comp z
    ((hasDerivAt_id z).sub_const a)).mul hgz.differentiableAt.hasDerivAt
  simp only [Function.comp_def, id_eq, Pi.mul_def] at hd
  rw [hz, hd.deriv]
  have hp : (z - a) ^ N = (z - a) ^ (N - 1) * (z - a) := by
    simpa using zpow_add_one₀ hne (N - 1)
  dsimp [u]
  rw [hp]
  ring

theorem exists_analytic_factor_iteratedDeriv {f g : ℂ → ℂ} {a : ℂ} (N : ℤ)
    (hg : AnalyticAt ℂ g a) (hf : f =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * g z) (k : ℕ) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧
      u a = (∏ i ∈ Finset.range k, ((N : ℂ) - i)) * g a ∧
      deriv^[k] f =ᶠ[𝓝[≠] a] fun z => (z - a) ^ (N - k) * u z := by
  induction k with
  | zero => exact ⟨g, hg, by simp, by simpa using hf⟩
  | succ k ih =>
    obtain ⟨v, hv, hva, hfv⟩ := ih
    obtain ⟨u, hu, hua, hfu⟩ := exists_analytic_factor_deriv (N - k) hv hfv
    refine ⟨u, hu, ?_, ?_⟩
    · rw [hua, hva, Finset.prod_range_succ]
      push_cast
      ring
    · simpa only [Function.iterate_succ_apply', Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub]
        using hfu

theorem eq_zero_of_analytic_zpow_mul_of_neg {f g : ℂ → ℂ} {a : ℂ} {N : ℤ}
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hfg : f =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * g z) (hN : N < 0) : g a = 0 := by
  by_contra hg0
  have ho : meromorphicOrderAt f a = (N : WithTop ℤ) :=
    (meromorphicOrderAt_eq_int_iff hf.meromorphicAt).mpr
      ⟨g, hg, hg0, by simpa only [smul_eq_mul] using hfg⟩
  have hnonneg := hf.meromorphicOrderAt_nonneg
  rw [ho] at hnonneg
  exact (not_le.mpr hN) (by exact_mod_cast hnonneg)

end DirichletL
