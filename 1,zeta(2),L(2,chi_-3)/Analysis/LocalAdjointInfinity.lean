import Analysis.LocalAdjoint

/-!
The inverse-coordinate calculation in CDT v2, proof of Lemma `14functions`,
the fifth local expansion and growth bound preceding equation `b3eq`.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem neg_sq_mul_deriv_comp_inv {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0)
    (hf : DifferentiableAt ℂ f z⁻¹) :
    -(z ^ 2) * deriv (fun t => f t⁻¹) z = deriv f z⁻¹ := by
  have hd := hf.hasDerivAt.comp z (hasDerivAt_inv hz)
  simp only [Function.comp_def] at hd
  rw [hd.deriv]
  field_simp

theorem exists_analytic_factor_neg_sq_mul_deriv {f g : ℂ → ℂ} (M : ℤ)
    (hg : AnalyticAt ℂ g 0) (hf : f =ᶠ[𝓝[≠] 0] fun z => z ^ M * g z) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u 0 ∧ u 0 = -(M : ℂ) * g 0 ∧
      (fun z => -(z ^ 2) * deriv f z) =ᶠ[𝓝[≠] 0] fun z => z ^ (M + 1) * u z := by
  obtain ⟨u, hu, hu0, hdu⟩ := exists_analytic_factor_deriv M hg (by simpa using hf)
  refine ⟨fun z => -u z, hu.neg, by simp [hu0], ?_⟩
  filter_upwards [hdu, self_mem_nhdsWithin] with z hd hz
  change z ≠ 0 at hz
  simp only [sub_zero] at hd
  rw [hd]
  have hp : z ^ 2 * z ^ (M - 1) = z ^ (M + 1) := by
    rw [← zpow_natCast z 2, ← zpow_add₀ hz]
    congr 1
    omega
  calc
    -(z ^ 2) * (z ^ (M - 1) * u z) = -(z ^ 2 * z ^ (M - 1)) * u z := by ring
    _ = z ^ (M + 1) * -u z := by rw [hp]; ring

private theorem backward_factor {f g v b : ℂ → ℂ} (M : ℤ)
    (hg : AnalyticAt ℂ g 0) (hv : AnalyticAt ℂ v 0)
    (hf : f =ᶠ[𝓝[≠] 0] fun z => z ^ M * g z)
    (hb : b =ᶠ[𝓝[≠] 0] fun z => z ^ (M + 1) * v z - (-(z ^ 2) * deriv f z)) :
    ∃ w : ℂ → ℂ, AnalyticAt ℂ w 0 ∧ w 0 = v 0 + (M : ℂ) * g 0 ∧
      b =ᶠ[𝓝[≠] 0] fun z => z ^ (M + 1) * w z := by
  obtain ⟨u, hu, hu0, hdu⟩ := exists_analytic_factor_neg_sq_mul_deriv M hg hf
  refine ⟨fun z => v z - u z, hv.sub hu, by simp [hu0], ?_⟩
  filter_upwards [hb, hdu] with z hbz hdz
  rw [hbz, hdz, mul_sub]

theorem exists_analytic_factor_adjointSystem_infinity {A U F : Fin 4 → ℂ → ℂ}
    {g : ℂ → ℂ} (M : ℤ) (hg : AnalyticAt ℂ g 0) (hU : ∀ i, AnalyticAt ℂ (U i) 0)
    (hA : ∀ i : Fin 4, A i =ᶠ[𝓝[≠] 0] fun z => z ^ (4 - (i : ℤ)) * U i z)
    (h3 : F 3 =ᶠ[𝓝[≠] 0] fun z => z ^ M * g z)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] 0,
      -(z ^ 2) * deriv (F i.succ) z = A i.succ z * F 3 z - F i.castSucc z) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧
      r 0 = adjointIndicial (fun i => U i 0) (-M) * g 0 ∧
      (fun z => -(z ^ 2) * deriv (F 0) z - A 0 z * F 3 z) =ᶠ[𝓝[≠] 0]
        fun z => z ^ (M + 4) * r z := by
  have hmul (i : Fin 4) : (fun z => A i z * F 3 z) =ᶠ[𝓝[≠] 0]
      fun z => z ^ (4 - (i : ℤ) + M) * (U i z * g z) := by
    filter_upwards [hA i, h3, self_mem_nhdsWithin] with z hAz h3z hz
    change z ≠ 0 at hz
    rw [hAz, h3z, zpow_add₀ hz]
    ring
  have step (i : Fin 3) (K : ℤ) (v : ℂ → ℂ) (hv : AnalyticAt ℂ v 0)
      (hF : F i.succ =ᶠ[𝓝[≠] 0] fun z => z ^ K * v z)
      (hK : K + 1 = 4 - ((i.succ : Fin 4) : ℤ) + M) :
      ∃ w : ℂ → ℂ, AnalyticAt ℂ w 0 ∧
        w 0 = U i.succ 0 * g 0 + (K : ℂ) * v 0 ∧
        F i.castSucc =ᶠ[𝓝[≠] 0] fun z => z ^ (K + 1) * w z := by
    apply backward_factor K hv ((hU _).mul hg) hF
    filter_upwards [hrec i, hmul i.succ] with z hr hm
    rw [← hK] at hm
    change F i.castSucc z = z ^ (K + 1) * (U i.succ z * g z) -
      (-(z ^ 2) * deriv (F i.succ) z)
    linear_combination hm + hr
  obtain ⟨v2, hv2, he2, hF2⟩ := step 2 M g hg h3 (by norm_num; omega)
  obtain ⟨v1, hv1, he1, hF1⟩ := step 1 (M + 1) v2 hv2 hF2 (by norm_num; omega)
  obtain ⟨v0, hv0, he0, hF0⟩ := step 0 (M + 1 + 1) v1 hv1 hF1 (by norm_num; omega)
  obtain ⟨u, hu, hu0, hdu⟩ := exists_analytic_factor_neg_sq_mul_deriv (M + 1 + 1 + 1) hv0 hF0
  refine ⟨fun z => u z - U 0 z * g z, hu.sub ((hU 0).mul hg), ?_, ?_⟩
  · simp only [hu0, he0, he1, he2, adjointIndicial]
    norm_num
    push_cast
    ring
  · filter_upwards [hdu, hmul 0] with z hd hm
    have hM : M + 1 + 1 + 1 + 1 = M + 4 := by omega
    have hM0 : 4 - ((0 : Fin 4) : ℤ) + M = M + 4 := by norm_num; omega
    rw [hM] at hd
    rw [hM0] at hm
    change -(z ^ 2) * deriv (F 0) z = _ at hd
    rw [hd, hm, mul_sub]

theorem adjointIndicial_neg_eq_zero_of_analytic {A U F : Fin 4 → ℂ → ℂ} {g R : ℂ → ℂ}
    (M : ℤ) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 ≠ 0) (hU : ∀ i, AnalyticAt ℂ (U i) 0)
    (hA : ∀ i : Fin 4, A i =ᶠ[𝓝[≠] 0] fun z => z ^ (4 - (i : ℤ)) * U i z)
    (h3 : F 3 =ᶠ[𝓝[≠] 0] fun z => z ^ M * g z)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] 0,
      -(z ^ 2) * deriv (F i.succ) z = A i.succ z * F 3 z - F i.castSucc z)
    (hR : AnalyticAt ℂ R 0)
    (hzero : (fun z => -(z ^ 2) * deriv (F 0) z - A 0 z * F 3 z) =ᶠ[𝓝[≠] 0] R)
    (hM : M < -4) : adjointIndicial (fun i => U i 0) (-M) = 0 := by
  obtain ⟨r, hr, hr0, hres⟩ := exists_analytic_factor_adjointSystem_infinity M hg hU hA h3 hrec
  have hrz := eq_zero_of_analytic_zpow_mul_of_neg hR hr
    (by simpa using hzero.symm.trans hres) (show M + 4 < 0 by omega)
  rw [hr0] at hrz
  exact (mul_eq_zero.mp hrz).resolve_right hg0

end DirichletL
