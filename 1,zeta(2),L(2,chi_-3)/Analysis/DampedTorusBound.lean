import Analysis.TorusBlockDamping

/-!
Positive exponent selection and uniform damping in CDT v2, supplied
TeX 4200-4228, and published UDC Sections 2.5.14-2.5.24. The integer
rounding and actual pointwise bound are independently checked before
-/

namespace DirichletL

theorem exists_damping_exponent {rate : ℝ} (hrate : 0 < rate) (A B : ℝ) :
    ∃ M : ℕ, 0 < M ∧ B - rate * (M : ℝ) ≤ A ∧
      (M : ℝ) ≤ max 0 (B - A) / rate + 2 := by
  let x := max 0 (B - A) / rate
  have hx : 0 ≤ x := div_nonneg (le_max_left _ _) hrate.le
  refine ⟨⌈x⌉₊ + 1, by omega, ?_, ?_⟩
  · have hceil := mul_le_mul_of_nonneg_left (Nat.le_ceil x) hrate.le
    have hmul : rate * x = max 0 (B - A) := by
      dsimp only [x]
      field_simp [hrate.ne']
    rw [hmul] at hceil
    have hmax := le_max_right (0 : ℝ) (B - A)
    push_cast
    nlinarith
  · have hceil := Nat.ceil_lt_add_one hx
    change ((⌈x⌉₊ + 1 : ℕ) : ℝ) ≤ x + 2
    push_cast
    linarith

theorem exists_block_damped_torus_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ b : Fin d → κ,
      (∀ k, ρ * (d : ℝ) ≤ ((Finset.univ.filter (fun j => b j = k)).card : ℝ)) →
      ∀ (G : (Fin d → AddCircle (2 * Real.pi)) → ℂ) (A B : ℝ),
      (∀ θ, ‖G θ‖ ≤ Real.exp B) →
      (∀ θ, (∀ k, HasIntervalDiscrepancyLE
        (fun i => torusUnitRepresentative
          (θ ((Finset.univ.filter (fun j => b j = k)).orderEmbOfFin rfl i))) ε) →
        ‖G θ‖ ≤ Real.exp A) →
      ∃ M : ℕ, 0 < M ∧ (M : ℝ) ≤ max 0 (B - A) / (c * (d : ℝ) ^ 2) + 2 ∧
        ∀ θ, ‖MvPolynomial.eval (fun i => fourier 1 (θ i))
          (blockVandermondePolynomial b M) * G θ‖ ≤
            Real.exp (A + (M : ℝ) * (d : ℝ) * Real.log (d : ℝ)) := by
  classical
  obtain ⟨c, hc, N, hN⟩ := exists_torus_blockVandermonde_damping (κ := κ) hε hρ
  refine ⟨c, hc, N + 1, ?_⟩
  intro d hd b hsize G A B hglobal hgood
  have hdpos : 0 < d := by omega
  have hrate : 0 < c * (d : ℝ) ^ 2 := mul_pos hc (sq_pos_of_pos (by exact_mod_cast hdpos))
  obtain ⟨M, hM, hcancel, hupper⟩ := exists_damping_exponent hrate A B
  refine ⟨M, hM, hupper, ?_⟩
  intro θ
  have hW := norm_eval_blockVandermondePolynomial_le b M hdpos
    (fun i => fourier 1 (θ i)) (fun i => Circle.norm_coe _)
  by_cases hgoodθ : ∀ k, HasIntervalDiscrepancyLE
      (fun i => torusUnitRepresentative
        (θ ((Finset.univ.filter (fun j => b j = k)).orderEmbOfFin rfl i))) ε
  · calc
      ‖MvPolynomial.eval (fun i => fourier 1 (θ i))
          (blockVandermondePolynomial b M) * G θ‖ ≤
          Real.exp ((M : ℝ) * (d : ℝ) * Real.log (d : ℝ)) * Real.exp A := by
        rw [norm_mul]
        exact mul_le_mul hW (hgood θ hgoodθ) (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  · obtain ⟨k, hk⟩ := not_forall.mp hgoodθ
    have hdamp := hN d (by omega) b θ ⟨k, hsize k, hk⟩ M hM
    have hcost : 0 ≤ (M : ℝ) * (d : ℝ) * Real.log (d : ℝ) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg M) (Nat.cast_nonneg d))
        (Real.log_nonneg (by exact_mod_cast hdpos))
    calc
      ‖MvPolynomial.eval (fun i => fourier 1 (θ i))
          (blockVandermondePolynomial b M) * G θ‖ ≤
          Real.exp (-c * (M : ℝ) * (d : ℝ) ^ 2) * Real.exp B := by
        rw [norm_mul]
        exact mul_le_mul hdamp.le (hglobal θ) (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (B - (c * (d : ℝ) ^ 2) * (M : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp A := Real.exp_le_exp.mpr hcancel
      _ ≤ _ := Real.exp_le_exp.mpr (le_add_of_nonneg_right hcost)

end DirichletL
