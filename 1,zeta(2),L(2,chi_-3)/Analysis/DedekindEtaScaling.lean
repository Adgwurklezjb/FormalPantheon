import Analysis.DedekindEtaWords

/-!
Scaled eta-square transformations for CDT v2 Section 11.1, equation `haupt`.
An exact integer matrix certificate transports the finite-word formula
to a positive integral multiple of the upper-half-plane argument.
-/

namespace DirichletL

open Complex Function.Periodic
open _root_.UpperHalfPlane hiding I
open scoped MatrixGroups

theorem qParam_one_nat_mul (n : ℕ) (τ : ℂ) : qParam 1 ((n : ℂ) * τ) = qParam 1 τ ^ n := by
  simp only [qParam, ofReal_one, div_one]
  rw [← exp_nat_mul]
  congr 1
  ring

theorem differentiableOn_dedekindEta_nat_mul (n : ℕ) (hn : 0 < n) :
    DifferentiableOn ℂ (fun τ : ℂ => dedekindEta ((n : ℂ) * τ)) {τ : ℂ | 0 < τ.im} := by
  apply differentiableOn_dedekindEta.comp
    ((differentiable_const _).mul differentiable_id).differentiableOn
  intro τ hτ
  simpa using mul_pos (show (0 : ℝ) < n by exact_mod_cast hn) hτ

theorem dedekindEta_sq_nat_mul_smul (n : ℕ) (hn : 0 < n) (γ : SL(2, ℤ))
    (w : List ℤ)
    (hmat : (modularWordMatrix w : Matrix (Fin 2) (Fin 2) ℤ) * !![(n : ℤ), 0; 0, 1] =
      !![(n : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ)) (τ : ℍ) :
    dedekindEta ((n : ℂ) * ((γ • τ : ℍ) : ℂ)) ^ 2 =
      dedekindEtaRoot ^ modularWordExponent w *
        ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) * dedekindEta ((n : ℂ) * τ) ^ 2 := by
  let A := modularWordMatrix w
  have h00 : A 0 0 * (n : ℤ) = (n : ℤ) * γ 0 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hmat
  have h01 : A 0 1 = (n : ℤ) * γ 0 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hmat
  have h10 : A 1 0 * (n : ℤ) = γ 1 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hmat
  have h11 : A 1 1 = γ 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hmat
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h00' : (A 0 0 : ℂ) = (γ 0 0 : ℂ) := by
    exact_mod_cast mul_right_cancel₀ hn0 (h00.trans (mul_comm _ _))
  have h01' : (A 0 1 : ℂ) = (n : ℂ) * (γ 0 1 : ℂ) := by exact_mod_cast h01
  have h10' : (A 1 0 : ℂ) * (n : ℂ) = (γ 1 0 : ℂ) := by exact_mod_cast h10
  have h11' : (A 1 1 : ℂ) = (γ 1 1 : ℂ) := by exact_mod_cast h11
  have hnτ : 0 < ((n : ℂ) * (τ : ℂ)).im := by
    simpa using mul_pos (show (0 : ℝ) < n by exact_mod_cast hn) τ.im_pos
  let σ : ℍ := ⟨(n : ℂ) * τ, hnτ⟩
  have hd : (A 1 0 : ℂ) * σ + (A 1 1 : ℂ) =
      (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) := by
    change (A 1 0 : ℂ) * ((n : ℂ) * τ) + (A 1 1 : ℂ) = _
    rw [← mul_assoc, h10', h11']
  have hnum : (A 0 0 : ℂ) * σ + (A 0 1 : ℂ) =
      (n : ℂ) * ((γ 0 0 : ℂ) * τ + (γ 0 1 : ℂ)) := by
    change (A 0 0 : ℂ) * ((n : ℂ) * τ) + (A 0 1 : ℂ) = _
    rw [h00', h01']
    ring
  have harg : (n : ℂ) * ((γ • τ : ℍ) : ℂ) = ((A • σ : ℍ) : ℂ) := by
    simp only [coe_specialLinearGroup_apply, algebraMap_int_eq, Int.coe_castRingHom,
      Complex.ofReal_intCast]
    change (n : ℂ) * (((γ 0 0 : ℂ) * τ + (γ 0 1 : ℂ)) /
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) =
        ((A 0 0 : ℂ) * σ + (A 0 1 : ℂ)) /
          ((A 1 0 : ℂ) * σ + (A 1 1 : ℂ))
    rw [hd, hnum, mul_div_assoc]
  have h := dedekindEta_sq_word_apply w σ
  change dedekindEta ((A • σ : ℍ) : ℂ) ^ 2 =
    dedekindEtaRoot ^ modularWordExponent w *
      ((A 1 0 : ℂ) * σ + (A 1 1 : ℂ)) * dedekindEta σ ^ 2 at h
  rw [← harg, hd] at h
  exact h

/-- Transport eta squared through an upper-triangular cusp certificate. -/
theorem dedekindEta_sq_affine_smul (n a d : ℕ) (ha : 0 < a) (hd : 0 < d) (b : ℤ)
    (γ : SL(2, ℤ)) (w : List ℤ)
    (hmat : !![(n : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) =
      (modularWordMatrix w : Matrix (Fin 2) (Fin 2) ℤ) * !![(a : ℤ), b; 0, (d : ℤ)])
    (τ : ℍ) :
    dedekindEta ((n : ℂ) * ((γ • τ : ℍ) : ℂ)) ^ 2 =
      dedekindEtaRoot ^ modularWordExponent w *
        (((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) / (d : ℂ)) *
          dedekindEta (((a : ℂ) * τ + (b : ℂ)) / (d : ℂ)) ^ 2 := by
  let A := modularWordMatrix w
  have h00 : (n : ℤ) * γ 0 0 = A 0 0 * (a : ℤ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 0) hmat
  have h01 : (n : ℤ) * γ 0 1 = A 0 0 * b + A 0 1 * (d : ℤ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 0 1) hmat
  have h10 : γ 1 0 = A 1 0 * (a : ℤ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hmat
  have h11 : γ 1 1 = A 1 0 * b + A 1 1 * (d : ℤ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hmat
  have h00' : (n : ℂ) * (γ 0 0 : ℂ) = (A 0 0 : ℂ) * (a : ℂ) := by exact_mod_cast h00
  have h01' : (n : ℂ) * (γ 0 1 : ℂ) =
      (A 0 0 : ℂ) * (b : ℂ) + (A 0 1 : ℂ) * (d : ℂ) := by exact_mod_cast h01
  have h10' : (γ 1 0 : ℂ) = (A 1 0 : ℂ) * (a : ℂ) := by exact_mod_cast h10
  have h11' : (γ 1 1 : ℂ) =
      (A 1 0 : ℂ) * (b : ℂ) + (A 1 1 : ℂ) * (d : ℂ) := by exact_mod_cast h11
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hσ : 0 < (((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ)).im := by
    simpa using div_pos (mul_pos (show (0 : ℝ) < a by exact_mod_cast ha) τ.im_pos)
      (show (0 : ℝ) < d by exact_mod_cast hd)
  let σ : ℍ := ⟨((a : ℂ) * τ + (b : ℂ)) / (d : ℂ), hσ⟩
  have hden : (A 1 0 : ℂ) * σ + (A 1 1 : ℂ) =
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) / (d : ℂ) := by
    change (A 1 0 : ℂ) * (((a : ℂ) * τ + (b : ℂ)) / (d : ℂ)) + (A 1 1 : ℂ) = _
    rw [h10', h11']
    field_simp
    ring
  have hnum : (A 0 0 : ℂ) * σ + (A 0 1 : ℂ) =
      (n : ℂ) * ((γ 0 0 : ℂ) * τ + (γ 0 1 : ℂ)) / (d : ℂ) := by
    change (A 0 0 : ℂ) * (((a : ℂ) * τ + (b : ℂ)) / (d : ℂ)) + (A 0 1 : ℂ) = _
    rw [mul_add, ← mul_assoc, h00', h01']
    field_simp
    ring
  have harg : (n : ℂ) * ((γ • τ : ℍ) : ℂ) = ((A • σ : ℍ) : ℂ) := by
    simp only [coe_specialLinearGroup_apply, algebraMap_int_eq, Int.coe_castRingHom,
      Complex.ofReal_intCast]
    change (n : ℂ) * (((γ 0 0 : ℂ) * τ + (γ 0 1 : ℂ)) /
      ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ))) =
        ((A 0 0 : ℂ) * σ + (A 0 1 : ℂ)) /
          ((A 1 0 : ℂ) * σ + (A 1 1 : ℂ))
    rw [hnum, hden, div_div_div_cancel_right₀ hd0, mul_div_assoc]
  have h := dedekindEta_sq_word_apply w σ
  change dedekindEta ((A • σ : ℍ) : ℂ) ^ 2 =
    dedekindEtaRoot ^ modularWordExponent w *
      ((A 1 0 : ℂ) * σ + (A 1 1 : ℂ)) * dedekindEta σ ^ 2 at h
  rw [← harg, hden] at h
  exact h

end DirichletL
