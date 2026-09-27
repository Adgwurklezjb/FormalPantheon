import Analysis.LocalExpansions

/-!
The local simple-pole obstruction for CDT v2, Lemma `seven`
(supplied TeX lines 7915-7958), in the differential presentation recorded
-/

namespace DirichletL

open Filter
open scoped Topology

/-- A first-order indicial equation without negative integral roots excludes poles. -/
theorem exists_analyticAt_eventuallyEq_of_meromorphic_regular_singular
    {f p q g : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a)
    (hp : AnalyticAt ℂ p a) (hq : AnalyticAt ℂ q a) (hg : AnalyticAt ℂ g a)
    (hind : ∀ N : ℤ, N < 0 → (N : ℂ) * p a + q a ≠ 0)
    (hfg : (fun z => (z - a) * p z * deriv f z + q z * f z) =ᶠ[𝓝[≠] a] g) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧ f =ᶠ[𝓝[≠] a] u := by
  rcases eq_or_ne (meromorphicOrderAt f a) ⊤ with htop | hfin
  · exact ⟨0, analyticAt_const, meromorphicOrderAt_eq_top_iff.mp htop⟩
  obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.mp hfin
  obtain ⟨v, hv, hv0, hfv⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hN.symm
  simp only [smul_eq_mul] at hfv
  have hnonneg : 0 ≤ N := by
    by_contra h
    have hneg : N < 0 := lt_of_not_ge h
    obtain ⟨u, hu, hua, hfu⟩ := exists_analytic_factor_deriv N hv hfv
    let w : ℂ → ℂ := fun z => p z * u z + q z * v z
    have hw : AnalyticAt ℂ w a := (hp.mul hu).add (hq.mul hv)
    have hwa : w a = ((N : ℂ) * p a + q a) * v a := by
      dsimp [w]
      rw [hua]
      ring
    have hgw : g =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * w z := by
      filter_upwards [hfg, hfu, hfv, self_mem_nhdsWithin] with z hgz huz hvz hza
      rw [← hgz, huz, hvz]
      have he : (z - a) ^ N = (z - a) * (z - a) ^ (N - 1) := by
        simpa [mul_comm] using zpow_add_one₀ (sub_ne_zero.mpr hza) (N - 1)
      dsimp [w]
      rw [he]
      ring
    have hz := eq_zero_of_analytic_zpow_mul_of_neg hg hw hgw hneg
    rw [hwa] at hz
    exact (mul_ne_zero (hind N hneg) hv0) hz
  lift N to ℕ using hnonneg
  refine ⟨fun z => (z - a) ^ N * v z,
    ((analyticAt_id.sub analyticAt_const).pow N).mul hv, ?_⟩
  simpa only [zpow_natCast] using hfv

/-- A regular zeroth-order term preserves the local obstruction for scaled derivatives. -/
theorem exists_analyticAt_eventuallyEq_of_analytic_mul_deriv_sub {f k g : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a) (hk : AnalyticAt ℂ k a) (hg : AnalyticAt ℂ g a)
    (hfg : (fun z => (z - a) * (deriv f z - k z * f z)) =ᶠ[𝓝[≠] a] g) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧ f =ᶠ[𝓝[≠] a] u ∧ g a = 0 := by
  have hex : ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧ f =ᶠ[𝓝[≠] a] u := by
    rcases eq_or_ne (meromorphicOrderAt f a) ⊤ with htop | hfin
    · exact ⟨0, analyticAt_const, meromorphicOrderAt_eq_top_iff.mp htop⟩
    obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.mp hfin
    obtain ⟨v, hv, hv0, hfv⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hN.symm
    simp only [smul_eq_mul] at hfv
    have hnonneg : 0 ≤ N := by
      by_contra h
      have hneg : N < 0 := lt_of_not_ge h
      obtain ⟨u, hu, hua, hfu⟩ := exists_analytic_factor_deriv N hv hfv
      let w : ℂ → ℂ := fun z => u z - (z - a) * k z * v z
      have hw : AnalyticAt ℂ w a :=
        hu.sub (((analyticAt_id.sub analyticAt_const).mul hk).mul hv)
      have hwa : w a = (N : ℂ) * v a := by simp [w, hua]
      have hgw : g =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * w z := by
        filter_upwards [hfg, hfu, hfv, self_mem_nhdsWithin] with z hgz huz hvz hza
        rw [← hgz, huz, hvz]
        have hp : (z - a) ^ N = (z - a) * (z - a) ^ (N - 1) := by
          simpa [mul_comm] using zpow_add_one₀ (sub_ne_zero.mpr hza) (N - 1)
        dsimp [w]
        rw [hp]
        ring
      have hz := eq_zero_of_analytic_zpow_mul_of_neg hg hw hgw hneg
      rw [hwa] at hz
      exact (mul_ne_zero (by exact_mod_cast ne_of_lt hneg) hv0) hz
    lift N to ℕ using hnonneg
    refine ⟨fun z => (z - a) ^ N * v z,
      ((analyticAt_id.sub analyticAt_const).pow N).mul hv, ?_⟩
    simpa only [zpow_natCast] using hfv
  obtain ⟨u, hu, hfu⟩ := hex
  refine ⟨u, hu, hfu, ?_⟩
  have he : g =ᶠ[𝓝[≠] a] fun z => (z - a) * (deriv u z - k z * u z) := by
    filter_upwards [hfg, eventuallyEq_deriv_of_punctured hfu, hfu] with z hgz hdu hfu
    rw [← hgz, hdu, hfu]
  have hu' : AnalyticAt ℂ (fun z => (z - a) * (deriv u z - k z * u z)) a :=
    (analyticAt_id.sub analyticAt_const).mul (hu.deriv.sub (hk.mul hu))
  have ha := hg.frequently_eq_iff_eventually_eq hu'
  have h := Filter.EventuallyEq.eq_of_nhds (ha.mp he.frequently)
  simpa using h

/-- An analytic scaled derivative has zero value at the center and an analytic primitive germ. -/
theorem exists_analyticAt_eventuallyEq_of_analytic_mul_deriv {f g : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a) (hg : AnalyticAt ℂ g a)
    (hfg : (fun z => (z - a) * deriv f z) =ᶠ[𝓝[≠] a] g) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧ f =ᶠ[𝓝[≠] a] u ∧ g a = 0 := by
  apply exists_analyticAt_eventuallyEq_of_analytic_mul_deriv_sub
    (k := fun _ => 0) hf analyticAt_const hg
  simpa only [zero_mul, sub_zero] using hfg

/-- An Euler equation with noninteger exponent has no nonzero meromorphic solution germ. -/
theorem eventuallyEq_zero_of_meromorphic_euler {f : ℂ → ℂ} {a c : ℂ}
    (hf : MeromorphicAt f a) (hc : ∀ N : ℤ, (N : ℂ) ≠ c)
    (hode : (fun z => (z - a) * deriv f z) =ᶠ[𝓝[≠] a] fun z => c * f z) :
    f =ᶠ[𝓝[≠] a] 0 := by
  rcases eq_or_ne (meromorphicOrderAt f a) ⊤ with htop | hfin
  · exact meromorphicOrderAt_eq_top_iff.mp htop
  obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.mp hfin
  obtain ⟨v, hv, hv0, hfv⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hN.symm
  simp only [smul_eq_mul] at hfv
  obtain ⟨u, hu, hua, hfu⟩ := exists_analytic_factor_deriv N hv hfv
  have he : u =ᶠ[𝓝[≠] a] fun z => c * v z := by
    filter_upwards [hode, hfu, hfv, self_mem_nhdsWithin] with z ho hu hv hz
    have hp : (z - a) ^ N = (z - a) * (z - a) ^ (N - 1) := by
      simpa [mul_comm] using zpow_add_one₀ (sub_ne_zero.mpr hz) (N - 1)
    apply mul_left_cancel₀ (zpow_ne_zero N (sub_ne_zero.mpr hz))
    rw [hu, hv] at ho
    calc
      (z - a) ^ N * u z = (z - a) * ((z - a) ^ (N - 1) * u z) := by rw [hp, mul_assoc]
      _ = c * ((z - a) ^ N * v z) := ho
      _ = (z - a) ^ N * (c * v z) := by ring
  have ha := tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] a)
    hu.continuousAt.continuousWithinAt
    (continuousAt_const.mul hv.continuousAt).continuousWithinAt he
  rw [hua] at ha
  exact ((hc N) (mul_right_cancel₀ hv0 ha)).elim

end DirichletL
