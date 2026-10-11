import Mathlib

/-!
Uniqueness for analytic solutions of linear matrix equations. These results
support the solution-space construction in CDT v2, Lemma `14functions`,
between its homogeneous comparison and equation `explicitode`.
-/

namespace DirichletL

open Filter
open scoped Topology Matrix

theorem eventuallyEq_zero_of_analytic_matrix_ode {I : Type*} [Fintype I]
    {A : ℂ → Matrix I I ℂ} {f : ℂ → I → ℂ} {z0 : ℂ}
    (hA : ContinuousAt A z0) (hf : AnalyticAt ℂ f z0) (hzero : f z0 = 0)
    (hode : ∀ᶠ z in 𝓝 z0, HasDerivAt f (A z *ᵥ f z) z) : f =ᶠ[𝓝 z0] 0 := by
  by_contra h
  obtain ⟨n, g, hg, hg0, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h
  cases n with
  | zero => exact hg0 (by simpa [hzero] using hfg.self_of_nhds.symm)
  | succ n =>
    let u : ℂ → I → ℂ := fun z =>
      (z - z0) • deriv g z + ((n + 1 : ℕ) : ℂ) • g z
    have hu : ContinuousAt u z0 :=
      ((continuousAt_id.sub continuousAt_const).smul hg.deriv.continuousAt).add
        (continuousAt_const.smul hg.continuousAt)
    have hm : Continuous (fun p : Matrix I I ℂ × (I → ℂ) => p.1 *ᵥ p.2) :=
      continuous_fst.matrix_mulVec continuous_snd
    have hv : ContinuousAt (fun z => (z - z0) • (A z *ᵥ g z)) z0 :=
      (continuousAt_id.sub continuousAt_const).smul
        (hm.continuousAt.comp (hA.prodMk hg.continuousAt))
    have he : u =ᶠ[𝓝[≠] z0] fun z => (z - z0) • (A z *ᵥ g z) := by
      filter_upwards [hfg.filter_mono nhdsWithin_le_nhds,
        (Filter.EventuallyEq.deriv hfg).filter_mono nhdsWithin_le_nhds,
        hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
        hode.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hfz hdz hgz hoz hz
      have hd := (((hasDerivAt_id z).sub_const z0).pow (n + 1)).smul
        hgz.differentiableAt.hasDerivAt
      simp only [id_eq, Pi.smul_def', Pi.pow_def] at hd
      have hdf : deriv f z = (z - z0) ^ n • u z := by
        rw [hdz, hd.deriv]
        ext i
        simp only [u, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.add_sub_cancel,
          id_eq, mul_one, pow_succ]
        ring
      have heq := hoz.deriv
      rw [hdf, hfz, Matrix.mulVec_smul, pow_succ, mul_smul] at heq
      exact (smul_right_inj (pow_ne_zero n (sub_ne_zero.mpr hz))).mp heq
    have hlim := tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z0)
      hu.continuousWithinAt hv.continuousWithinAt he
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    exact hg0 ((smul_eq_zero.mp (by simpa [u] using hlim)).resolve_left hn)

theorem eventuallyEq_of_analytic_matrix_ode {I : Type*} [Fintype I]
    {A : ℂ → Matrix I I ℂ} {f g : ℂ → I → ℂ} {z0 : ℂ}
    (hA : ContinuousAt A z0) (hf : AnalyticAt ℂ f z0) (hg : AnalyticAt ℂ g z0)
    (hinit : f z0 = g z0)
    (hfode : ∀ᶠ z in 𝓝 z0, HasDerivAt f (A z *ᵥ f z) z)
    (hgode : ∀ᶠ z in 𝓝 z0, HasDerivAt g (A z *ᵥ g z) z) : f =ᶠ[𝓝 z0] g := by
  have hz := eventuallyEq_zero_of_analytic_matrix_ode hA (hf.sub hg)
    (by simpa only [Pi.sub_apply, sub_eq_zero] using hinit) (by
      filter_upwards [hfode, hgode] with z hfz hgz
      simpa only [Pi.sub_apply, Matrix.mulVec_sub] using hfz.sub hgz)
  filter_upwards [hz] with z hz
  exact sub_eq_zero.mp hz

theorem linearIndependent_iff_initialValue_of_analytic_matrix_ode
    {I J : Type*} [Fintype I] [Fintype J] {A : ℂ → Matrix I I ℂ}
    {f : J → ℂ → I → ℂ} {U : Set ℂ} {z0 : ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hz0 : z0 ∈ U)
    (hA : ContinuousAt A z0) (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hode : ∀ j z, z ∈ U → HasDerivAt (f j) (A z *ᵥ f j z) z) :
    LinearIndependent ℂ (fun j => fun z : U => f j z) ↔
      LinearIndependent ℂ (fun j => f j z0) := by
  classical
  rw [Fintype.linearIndependent_iff, Fintype.linearIndependent_iff]
  constructor
  · intro h c hc
    let F : ℂ → I → ℂ := fun z => ∑ j, c j • f j z
    have hF : AnalyticOnNhd ℂ F U := by
      convert
        Finset.univ.analyticOnNhd_sum (fun j _ z hz => (hf j z hz).const_smul (c := c j))
        using 1
      ext z i
      simp [F]
    have hFode : ∀ᶠ z in 𝓝 z0, HasDerivAt F (A z *ᵥ F z) z := by
      filter_upwards [hU.mem_nhds hz0] with z hz
      convert
        (HasDerivAt.sum (u := Finset.univ) (fun j _ => (hode j z hz).const_smul (c j)))
        using 1
      · ext w i
        simp [F]
      · simp only [F, ← Matrix.mulVecLin_apply, map_sum, map_smul]
    have hlocal := eventuallyEq_zero_of_analytic_matrix_ode hA (hF z0 hz0) hc hFode
    have hfull := hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz0 hlocal
    apply h c
    funext z
    simpa only [F, Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using hfull z.property
  · intro h c hc
    apply h c
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using
      congrFun hc (⟨z0, hz0⟩ : U)

end DirichletL
