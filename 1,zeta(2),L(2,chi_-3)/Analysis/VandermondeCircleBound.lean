import Analysis.RegularizedCircleEnergy

/-!
Finite-circle estimates for the Vandermonde dampener in CDT v2, supplied
TeX 4040-4067, and published UDC Lemma 2.5.9. The precise meanings and
-/

namespace DirichletL

open scoped Classical ComplexConjugate

theorem sum_sum_eq_diag_add_two_mul_sum_Ioi {d : ℕ} (f : Fin d → Fin d → ℝ)
    (hsym : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) + 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
  letI : DecidableEq (Fin d) := LinearOrder.toDecidableEq
  have hoff := Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag f
  have hsplit (i : Fin d) : (∑ j, f i j) = f i i + ∑ j ∈ {i}ᶜ, f j i := by
    calc
      (∑ j, f i j) = ∑ j, f j i := Finset.sum_congr rfl (fun j _ => hsym i j)
      _ = f i i + ∑ j ∈ {i}ᶜ, f j i := by
        simpa only [Finset.sum_singleton] using
          (Finset.sum_add_sum_compl {i} (fun j => f j i)).symm
  have hoff' : (∑ i, ∑ j ∈ {i}ᶜ, f j i) = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
    calc
      _ = ∑ i, ∑ j ∈ Finset.Ioi i, (f j i + f i j) := hoff.symm
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsym j i]
        ring
  calc
    _ = (∑ i, f i i) + (∑ i, ∑ j ∈ {i}ᶜ, f j i) := by
      simp_rw [hsplit]
      exact Finset.sum_add_distrib
    _ = _ := by rw [hoff']

theorem log_norm_vandermonde_eq_sum {d : ℕ} (z : Fin d → ℂ) (hinj : Function.Injective z) :
    Real.log ‖(Matrix.vandermonde z).det‖ =
      ∑ i, ∑ j ∈ Finset.Ioi i, Real.log ‖z j - z i‖ := by
  have hfactor (i j : Fin d) (hij : i < j) : ‖z j - z i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hinj.ne hij.ne'))
  rw [Matrix.det_vandermonde]
  simp_rw [norm_prod]
  rw [Real.log_prod _ _ (fun i _ => Finset.prod_ne_zero_iff.mpr
    (fun j hj => hfactor i j (Finset.mem_Ioi.mp hj)))]
  apply Finset.sum_congr rfl
  intro i hi
  exact Real.log_prod _ _ (fun j hj => hfactor i j (Finset.mem_Ioi.mp hj))

theorem log_norm_vandermonde_le_regularized_energy {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hinj : Function.Injective z)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (m : ℕ) :
    Real.log ‖(Matrix.vandermonde z).det‖ ≤
      -(r ^ m / (m : ℝ) * ‖∑ i, z i ^ m‖ ^ 2) / 2 -
        (d : ℝ) * Real.log (1 - r) / 2 - (d : ℝ) * ((d : ℝ) - 1) * Real.log r / 4 := by
  let f (i j : Fin d) : ℝ := Real.log ‖1 - (r : ℂ) * (z i * conj (z j))‖
  have hsym (i j : Fin d) : f i j = f j i := by
    have hc : conj (1 - (r : ℂ) * (z i * conj (z j))) =
        1 - (r : ℂ) * (z j * conj (z i)) := by
      simp [mul_comm]
    dsimp only [f]
    rw [← hc, Complex.norm_conj]
  have hdiag (i : Fin d) : f i i = Real.log (1 - r) := by
    dsimp only [f]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz i]
    simp only [one_pow, Complex.ofReal_one, mul_one]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr1)]
  have hsplit := sum_sum_eq_diag_add_two_mul_sum_Ioi f hsym
  have hdiagsum : (∑ i, f i i) = (d : ℝ) * Real.log (1 - r) := by simp [hdiag]
  rw [hdiagsum] at hsplit
  have henergy := fourier_mode_le_regularized_circle_energy z hz hr.le hr1 m
  change r ^ m / (m : ℝ) * ‖∑ i, z i ^ m‖ ^ 2 ≤ -(∑ i, ∑ j, f i j) at henergy
  rw [hsplit] at henergy
  have hcard : (∑ i : Fin d, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) =
      (d : ℝ) * ((d : ℝ) - 1) / 2 := by
    have h := sum_sum_eq_diag_add_two_mul_sum_Ioi (fun _ _ : Fin d => (1 : ℝ))
      (fun _ _ => rfl)
    have heq : (d : ℝ) ^ 2 = (d : ℝ) +
        2 * (∑ i : Fin d, ∑ _j ∈ Finset.Ioi i, (1 : ℝ)) := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, pow_two] using h
    nlinarith only [heq]
  have hpair : (∑ i, ∑ j ∈ Finset.Ioi i, Real.log ‖z j - z i‖) ≤
      (∑ i, ∑ j ∈ Finset.Ioi i, f i j) -
        ((d : ℝ) * ((d : ℝ) - 1) / 2) * (Real.log r / 2) := by
    calc
      (∑ i, ∑ j ∈ Finset.Ioi i, Real.log ‖z j - z i‖) ≤
          ∑ i, ∑ j ∈ Finset.Ioi i, (f i j - Real.log r / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have h := log_norm_sub_le_log_norm_regularized (hz i) (hz j)
          (hinj.ne (Finset.mem_Ioi.mp hj).ne) hr
        rw [norm_sub_rev (z i) (z j)] at h
        exact h
      _ = (∑ i, ∑ j ∈ Finset.Ioi i, f i j) -
          ((d : ℝ) * ((d : ℝ) - 1) / 2) * (Real.log r / 2) := by
        simp only [Finset.sum_sub_distrib]
        congr 1
        rw [← hcard]
        simp only [Finset.sum_mul, one_mul]
  rw [log_norm_vandermonde_eq_sum z hinj]
  nlinarith only [henergy, hpair]

theorem norm_vandermonde_le_regularized_energy {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (m : ℕ) :
    ‖(Matrix.vandermonde z).det‖ ≤ Real.exp
      (-(r ^ m / (m : ℝ) * ‖∑ i, z i ^ m‖ ^ 2) / 2 -
        (d : ℝ) * Real.log (1 - r) / 2 - (d : ℝ) * ((d : ℝ) - 1) * Real.log r / 4) := by
  by_cases hinj : Function.Injective z
  · have hpos : 0 < ‖(Matrix.vandermonde z).det‖ :=
      norm_pos_iff.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
    exact (Real.log_le_iff_le_exp hpos).mp
      (log_norm_vandermonde_le_regularized_energy z hz hinj hr hr1 m)
  · have hdet : (Matrix.vandermonde z).det = 0 := by
      by_contra h
      exact hinj (Matrix.det_vandermonde_ne_zero_iff.mp h)
    rw [hdet, norm_zero]
    exact (Real.exp_pos _).le

end DirichletL
