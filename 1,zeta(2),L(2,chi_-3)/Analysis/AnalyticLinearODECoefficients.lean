import Mathlib

/-!
Convergent coefficient construction for complex linear matrix ODEs.
This supports the homogeneous solution space in CDT v2, Lemma `14functions`,
before equation `explicitode`.
-/

namespace DirichletL

open scoped Matrix NNReal ENNReal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {I : Type*} [Fintype I]

/-- The Taylor coefficients of the solution of `f' = A f` with initial vector `v`. -/
noncomputable def matrixODECoeff (A : ℕ → Matrix I I ℂ) (v : I → ℂ) : ℕ → I → ℂ
  | 0 => v
  | n + 1 => ((n + 1 : ℕ) : ℂ)⁻¹ •
      ∑ k ∈ Finset.range (n + 1), A k *ᵥ matrixODECoeff A v (n - k)
termination_by n => n
decreasing_by omega

@[simp]
theorem matrixODECoeff_zero (A : ℕ → Matrix I I ℂ) (v : I → ℂ) :
    matrixODECoeff A v 0 = v := by
  rw [matrixODECoeff]

theorem matrixODECoeff_succ (A : ℕ → Matrix I I ℂ) (v : I → ℂ) (n : ℕ) :
    matrixODECoeff A v (n + 1) = ((n + 1 : ℕ) : ℂ)⁻¹ •
      ∑ k ∈ Finset.range (n + 1), A k *ᵥ matrixODECoeff A v (n - k) := by
  rw [matrixODECoeff]

theorem succ_smul_matrixODECoeff (A : ℕ → Matrix I I ℂ) (v : I → ℂ) (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) • matrixODECoeff A v (n + 1) =
      ∑ k ∈ Finset.range (n + 1), A k *ᵥ matrixODECoeff A v (n - k) := by
  rw [matrixODECoeff_succ, smul_smul, mul_inv_cancel₀, one_smul]
  exact_mod_cast Nat.succ_ne_zero n

private theorem norm_mulVec_le_card (A : Matrix I I ℂ) (v : I → ℂ) :
    ‖A *ᵥ v‖ ≤ Fintype.card I * ‖A‖ * ‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : I, ‖A‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i))
        (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = Fintype.card I * ‖A‖ * ‖v‖ := by simp [mul_assoc]

/-- A geometric coefficient bound for the linear ODE recurrence. -/
theorem norm_matrixODECoeff_le {A : ℕ → Matrix I I ℂ} (v : I → ℂ)
    {M R C : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hC : 0 < C)
    (hRC : R ≤ C) (hMC : Fintype.card I * M ≤ C)
    (hA : ∀ n, ‖A n‖ ≤ M * R ^ n) (n : ℕ) :
    ‖matrixODECoeff A v n‖ ≤ ‖v‖ * C ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
          ‖A k *ᵥ matrixODECoeff A v (n - k)‖ ≤ C * (‖v‖ * C ^ n) := by
        have hk' : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
        calc
          ‖A k *ᵥ matrixODECoeff A v (n - k)‖ ≤
              Fintype.card I * ‖A k‖ * ‖matrixODECoeff A v (n - k)‖ :=
            norm_mulVec_le_card _ _
          _ ≤ (Fintype.card I * (M * C ^ k)) * (‖v‖ * C ^ (n - k)) := by
            gcongr
            · exact (hA k).trans (mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ hR hRC k) hM)
            · exact ih (n - k) (by omega)
          _ = (Fintype.card I * M) * (‖v‖ * C ^ n) := by
            calc
              _ = (Fintype.card I * M) * (‖v‖ * (C ^ k * C ^ (n - k))) := by ring
              _ = _ := by rw [← pow_add, Nat.add_sub_of_le hk']
          _ ≤ C * (‖v‖ * C ^ n) := mul_le_mul_of_nonneg_right hMC (by positivity)
      have hsum : ‖∑ k ∈ Finset.range (n + 1),
          A k *ᵥ matrixODECoeff A v (n - k)‖ ≤
          (n + 1 : ℕ) * (C * (‖v‖ * C ^ n)) := by
        exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans_eq (by simp))
      rw [matrixODECoeff_succ, norm_smul, norm_inv, Complex.norm_natCast]
      calc
        _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ *
            ((n + 1 : ℕ) * (C * (‖v‖ * C ^ n))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = ‖v‖ * C ^ (n + 1) := by
          rw [inv_mul_cancel_left₀ (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0), pow_succ]
          ring

/-- The canonical multilinear series for the matrix ODE coefficients. -/
noncomputable def matrixODESeries (A : ℕ → Matrix I I ℂ) (v : I → ℂ) :
    FormalMultilinearSeries ℂ ℂ (I → ℂ) :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (matrixODECoeff A v n)

@[simp]
theorem coeff_matrixODESeries (A : ℕ → Matrix I I ℂ) (v : I → ℂ) (n : ℕ) :
    (matrixODESeries A v).coeff n = matrixODECoeff A v n := by
  simp [matrixODESeries, FormalMultilinearSeries.coeff]

/-- Analytic coefficient matrices give a convergent solution series for every initial vector. -/
theorem matrixODESeries_radius_pos {A : ℕ → Matrix I I ℂ} (v : I → ℂ)
    {M R : ℝ} (hM : 0 < M) (hR : 0 < R) (hA : ∀ n, ‖A n‖ ≤ M * R ^ n) :
    0 < (matrixODESeries A v).radius := by
  let C : ℝ := max 1 (max R (Fintype.card I * M))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hRC : R ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hMC : Fintype.card I * M ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  let r : ℝ≥0 := ⟨C⁻¹, inv_nonneg.mpr hC.le⟩
  have hr : 0 < (r : ℝ≥0∞) := by
    exact_mod_cast (inv_pos.mpr hC : 0 < C⁻¹)
  apply hr.trans_le
  apply (matrixODESeries A v).le_radius_of_bound ‖v‖
  intro n
  rw [FormalMultilinearSeries.norm_apply_eq_norm_coef, coeff_matrixODESeries]
  calc
    ‖matrixODECoeff A v n‖ * (r : ℝ) ^ n ≤ (‖v‖ * C ^ n) * (r : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right
        (norm_matrixODECoeff_le v hM.le hR.le hC hRC hMC hA n) (by positivity)
    _ = ‖v‖ := by
      change (‖v‖ * C ^ n) * (C⁻¹) ^ n = _
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hC.ne', one_pow, mul_one]

end DirichletL
