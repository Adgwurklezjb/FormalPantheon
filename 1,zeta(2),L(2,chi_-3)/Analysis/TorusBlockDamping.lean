import Analysis.BlockVandermondeDamping

/-!
The angle coordinates in the damped Cauchy integral, CDT v2 TeX 4069-4137.
The pointwise period transport and seam convention precede these proofs
-/

namespace DirichletL

attribute [local instance] fact_one_pos

/-- The representative in `[0, 1)` after rescaling a period-`2 * π` angle to period one. -/
noncomputable def torusUnitRepresentative (θ : AddCircle (2 * Real.pi)) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0
    (AddCircle.equivAddCircle (2 * Real.pi) 1 Real.two_pi_pos.ne' one_ne_zero θ) : ℝ)

theorem torusUnitRepresentative_mem_Ico (θ : AddCircle (2 * Real.pi)) :
    torusUnitRepresentative θ ∈ Set.Ico (0 : ℝ) 1 := by
  simpa only [torusUnitRepresentative, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0
      (AddCircle.equivAddCircle (2 * Real.pi) 1 Real.two_pi_pos.ne' one_ne_zero θ)).property

theorem fourier_torusUnitRepresentative (θ : AddCircle (2 * Real.pi)) :
    fourier 1 (torusUnitRepresentative θ : AddCircle (1 : ℝ)) = fourier 1 θ := by
  let u := AddCircle.equivAddCircle (2 * Real.pi) 1 Real.two_pi_pos.ne' one_ne_zero θ
  have hu : (torusUnitRepresentative θ : AddCircle (1 : ℝ)) = u :=
    (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply u
  rw [hu]
  dsimp only [u]
  induction θ using QuotientAddGroup.induction_on
  simp only [AddCircle.equivAddCircle_apply_mk, fourier_coe_apply, mul_one, div_one]
  congr 1
  push_cast
  ring

theorem exists_torus_blockVandermonde_damping {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ b : Fin d → κ,
      ∀ θ : Fin d → AddCircle (2 * Real.pi),
      (∃ k, ρ * (d : ℝ) ≤ ((Finset.univ.filter (fun j => b j = k)).card : ℝ) ∧
        ¬HasIntervalDiscrepancyLE
          (fun i => torusUnitRepresentative
            (θ ((Finset.univ.filter (fun j => b j = k)).orderEmbOfFin rfl i))) ε) →
      ∀ M : ℕ, 0 < M →
        ‖MvPolynomial.eval (fun i => fourier 1 (θ i)) (blockVandermondePolynomial b M)‖ <
          Real.exp (-c * (M : ℝ) * (d : ℝ) ^ 2) := by
  obtain ⟨c, hc, N, hN⟩ := exists_blockVandermonde_damping (κ := κ) hε hρ
  refine ⟨c, hc, N, ?_⟩
  intro d hd b θ hbad M hM
  have ht (i : Fin d) : torusUnitRepresentative (θ i) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(torusUnitRepresentative_mem_Ico _).1, (torusUnitRepresentative_mem_Ico _).2.le⟩
  simpa only [fourier_torusUnitRepresentative] using
    hN d hd b (fun i => torusUnitRepresentative (θ i)) ht hbad M hM

end DirichletL
