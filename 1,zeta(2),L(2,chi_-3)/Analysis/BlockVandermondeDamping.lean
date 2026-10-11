import Analysis.BlockVandermondeBound
import Analysis.IntervalVandermondeDamping

/-!
Uniform damping of the literal block multiplier in CDT v2, supplied
TeX 4069-4092. Constants, dimension thresholds, and positive powers are
-/

namespace DirichletL

open Filter

attribute [local instance] fact_one_pos

theorem exists_blockVandermonde_damping {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ b : Fin d → κ,
      ∀ t : Fin d → ℝ, (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) →
      (∃ k, ρ * (d : ℝ) ≤ ((Finset.univ.filter (fun j => b j = k)).card : ℝ) ∧
        ¬HasIntervalDiscrepancyLE
          (fun i => t ((Finset.univ.filter (fun j => b j = k)).orderEmbOfFin rfl i)) ε) →
      ∀ M : ℕ, 0 < M →
        ‖MvPolynomial.eval (fun i => fourier 1 (t i : AddCircle (1 : ℝ)))
          (blockVandermondePolynomial b M)‖ < Real.exp (-c * (M : ℝ) * (d : ℝ) ^ 2) := by
  obtain ⟨c0, hc0, N0, hN0⟩ := exists_vandermonde_damping_of_interval_discrepancy hε
  let c := c0 * ρ ^ 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hev : ∀ᶠ d : ℕ in atTop, ‖Real.log (d : ℝ)‖ ≤ c * ‖(d : ℝ)‖ :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop).eventually
      (Real.isLittleO_log_id_atTop.def hc)
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp hev
  obtain ⟨Nsize, hNsize⟩ := exists_nat_ge ((N0 : ℝ) / ρ)
  refine ⟨c, hc, max Nsize Nlog + 1, ?_⟩
  intro d hd b t ht hbad M hM
  obtain ⟨k, hsize, hdisc⟩ := hbad
  let s := Finset.univ.filter (fun j => b j = k)
  have hdpos : 0 < d := by omega
  have hds : Nsize ≤ d := by omega
  have hdl : Nlog ≤ d := by omega
  have hdR0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsd : N0 ≤ s.card := by
    have hsize0 : (N0 : ℝ) ≤ ρ * (Nsize : ℝ) := by
      simpa only [mul_comm] using (div_le_iff₀ hρ).mp hNsize
    have hsize1 : (N0 : ℝ) ≤ (s.card : ℝ) :=
      (hsize0.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hds) hρ.le)).trans hsize
    exact_mod_cast hsize1
  have hdet := hN0 s.card hsd (fun i => t (s.orderEmbOfFin rfl i))
    (fun i => ht _) hdisc
  have hW := norm_eval_blockVandermondePolynomial_lt_of_block b M hM hdpos
    (fun i => fourier 1 (t i : AddCircle (1 : ℝ))) (fun i => Circle.norm_coe _)
    k (-c0 * (s.card : ℝ) ^ 2) hdet
  have hlog : Real.log (d : ℝ) ≤ c * (d : ℝ) :=
    (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hdR0] using hNlog d hdl)
  have hsq : (ρ * (d : ℝ)) ^ 2 ≤ (s.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hρ.le (Nat.cast_nonneg d)) hsize 2
  have hexponent : -c0 * (s.card : ℝ) ^ 2 + (d : ℝ) * Real.log (d : ℝ) ≤
      -c * (d : ℝ) ^ 2 := by
    have hlarge := mul_le_mul_of_nonneg_left hsq hc0.le
    have hsmall := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d)
    dsimp only [c] at hsmall ⊢
    nlinarith
  refine hW.trans_le (Real.exp_le_exp.mpr ?_)
  calc
    (M : ℝ) * (-c0 * (s.card : ℝ) ^ 2 + (d : ℝ) * Real.log (d : ℝ)) ≤
        (M : ℝ) * (-c * (d : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hexponent (Nat.cast_nonneg M)
    _ = -c * (M : ℝ) * (d : ℝ) ^ 2 := by ring

end DirichletL
