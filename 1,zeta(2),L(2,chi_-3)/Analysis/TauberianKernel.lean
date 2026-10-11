import Mathlib

/-!
Logarithmic weights for the Wiener-Ikehara proof used in CDT v2's lcm
input (supplied TeX 3291-3310). Adapted from the PrimeNumberTheoremAnd
contributors, Wiener.lean at revision 0766218b21b11ddf24103352ece7f0cb730945e0,
lines 1139-1203 and 1308-1393. The original source and Apache 2.0 license
explicit endpoint cases, and removal of unused polynomial helpers.
-/

namespace DirichletL

open Real MeasureTheory Filter Set
open scoped Topology

/-- The logarithmic kernel, with the standard totalized value at zero. -/
noncomputable def tauberianLogKernel (a t : ℝ) : ℝ :=
  (t * (1 + (a * Real.log t) ^ 2))⁻¹

theorem tauberianLogKernel_zero (a : ℝ) : tauberianLogKernel a 0 = 0 := by
  simp [tauberianLogKernel]

theorem tauberianLogKernel_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ tauberianLogKernel a t := by
  rcases ht.eq_or_lt with rfl | ht
  · exact le_of_eq (tauberianLogKernel_zero a).symm
  · unfold tauberianLogKernel
    positivity

theorem hasDerivAt_tauberianLogKernel (a : ℝ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (tauberianLogKernel a)
      (-(a ^ 2 * (Real.log t + 1) ^ 2 + (1 - a) * (1 + a)) *
        tauberianLogKernel a t ^ 2) t := by
  have hden : t * (1 + (a * Real.log t) ^ 2) ≠ 0 := mul_ne_zero ht (by positivity)
  have hlog := (Real.hasDerivAt_log ht).const_mul a
  have hsq : HasDerivAt (fun t : ℝ => (a * Real.log t) ^ 2)
      (2 * a ^ 2 * t⁻¹ * Real.log t) t := by
    convert hlog.pow 2 using 1
    ring
  have hmul : HasDerivAt (fun t : ℝ => t * (1 + (a * Real.log t) ^ 2))
      (1 + 2 * a ^ 2 * Real.log t + a ^ 2 * Real.log t ^ 2) t := by
    convert (hasDerivAt_id t).mul (hsq.const_add 1) using 1
    simp only [id_eq]
    field_simp
    ring
  convert hmul.inv hden using 1
  dsimp only [tauberianLogKernel]
  field_simp
  ring

theorem continuousOn_tauberianLogKernel (a : ℝ) :
    ContinuousOn (tauberianLogKernel a) (Ioi 0) :=
  fun _ ht => (hasDerivAt_tauberianLogKernel a ht.ne').continuousAt.continuousWithinAt

theorem antitoneOn_tauberianLogKernel {a : ℝ} (ha : a ∈ Ioo (-1) 1) :
    AntitoneOn (tauberianLogKernel a) (Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _)
    (continuousOn_tauberianLogKernel a)
    (fun t ht => (hasDerivAt_tauberianLogKernel a
      (ne_of_gt (interior_subset ht))).hasDerivWithinAt)
  intro t _
  have hm : 0 ≤ 1 - a := by linarith [ha.2]
  have hp : 0 ≤ 1 + a := by linarith [ha.1]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg hm hp))) (sq_nonneg _)

theorem integrableOn_mul_tauberianLogKernel_and_integral {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * tauberianLogKernel b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * tauberianLogKernel b (t / c) = a * c / b * π) := by

  rw [integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)]
  simp only [tauberianLogKernel]

  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹

  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert (l1 x hx).const_mul (a * c / b) using 1
    dsimp only [g']
    field_simp
    <;> ring
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]

  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id

  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp at hx1 ⊢ ; positivity
    · simp [abs_eq_self.mpr hc.le] at hx2 ⊢ ; rwa [div_lt_iff₀ hc, mul_comm]

  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    convert (show ContinuousWithinAt g₀ (Ioi 0) 0 from k2).insert using 1
    ext t
    simp only [mem_Ici, mem_insert_iff, mem_Ioi, le_iff_eq_or_lt, eq_comm]

  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x)
    exact mul_nonneg ha.le (tauberianLogKernel_nonneg b (div_nonneg hx.le hc.le))

  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring


/-- The weight at the precise Fourier normalization 1/(2*pi). -/
noncomputable def tauberianWeight (x t : ℝ) : ℝ :=
  t⁻¹ * (1 + (1 / (2 * Real.pi) * Real.log (t / x)) ^ 2)⁻¹

theorem tauberianWeight_zero (x : ℝ) : tauberianWeight x 0 = 0 := by
  simp [tauberianWeight]

theorem tauberianWeight_nonneg (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ tauberianWeight x t := by
  unfold tauberianWeight
  positivity

theorem tauberianWeight_eq_logKernel {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    tauberianWeight x t = x⁻¹ * tauberianLogKernel (1 / (2 * Real.pi)) (t / x) := by
  simp only [tauberianWeight, tauberianLogKernel, mul_inv_rev, inv_div]
  field_simp

theorem tauberianWeight_nat_le_one (x : ℝ) (n : ℕ) : tauberianWeight x n ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn, tauberianWeight_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hs : (1 : ℝ) ≤ 1 + (1 / (2 * Real.pi) * Real.log ((n : ℝ) / x)) ^ 2 := by
    exact le_add_of_nonneg_right (sq_nonneg _)
  unfold tauberianWeight
  rw [← mul_inv]
  apply inv_le_one_of_one_le₀
  simpa only [one_mul] using mul_le_mul hn1 hs zero_le_one (by positivity)

theorem antitoneOn_tauberianWeight {x : ℝ} (hx : 0 < x) :
    AntitoneOn (tauberianWeight x) (Ioi 0) := by
  have ha : 1 / (2 * Real.pi) ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · have : 0 < 1 / (2 * Real.pi) := by positivity
      linarith
    · apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [Real.two_le_pi]
  intro s hs t ht hst
  rw [tauberianWeight_eq_logKernel hx.ne', tauberianWeight_eq_logKernel hx.ne']
  exact mul_le_mul_of_nonneg_left
    (antitoneOn_tauberianLogKernel ha (div_pos hs hx) (div_pos ht hx)
      ((div_le_div_iff_of_pos_right hx).mpr hst)) (inv_nonneg.mpr hx.le)

theorem integrableOn_tauberianWeight_and_integral {x : ℝ} (hx : 0 < x) :
    IntegrableOn (tauberianWeight x) (Ici 0) ∧
      (∫ t in Ioi 0, tauberianWeight x t) = 2 * Real.pi ^ 2 := by
  have hfun : tauberianWeight x = fun t =>
      x⁻¹ * tauberianLogKernel (1 / (2 * Real.pi)) (t / x) :=
    funext (tauberianWeight_eq_logKernel hx.ne')
  rw [hfun]
  obtain ⟨hi, hv⟩ := integrableOn_mul_tauberianLogKernel_and_integral
    (inv_pos.mpr hx) (show 0 < 1 / (2 * Real.pi) by positivity) hx
  refine ⟨hi, ?_⟩
  rw [hv]
  field_simp

end DirichletL
