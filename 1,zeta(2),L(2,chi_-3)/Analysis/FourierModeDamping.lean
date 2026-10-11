import Analysis.VandermondeCircleBound

/-!
The fixed constants in the finite-mode implementation of CDT v2, supplied
TeX 4054-4067, and published UDC Lemma 2.5.9. The radius choice, strict
margin, and dimension order are checked before these proofs in
-/

namespace DirichletL

theorem exists_regularized_circle_radius {K : ℕ} (hK : 0 < K) {a : ℝ} (ha : 0 < a) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ (1 / 2 : ℝ) ≤ r ^ K ∧
      -Real.log r ≤ a ^ 2 / (2 * (K : ℝ)) := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  let s := min (Real.log 2 / (K : ℝ)) (a ^ 2 / (2 * (K : ℝ)))
  have hs : 0 < s := lt_min
    (div_pos (Real.log_pos (by norm_num)) hKR) (by positivity)
  refine ⟨Real.exp (-s), Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos hs), ?_, ?_⟩
  · have hbound : s * (K : ℝ) ≤ Real.log 2 :=
      (le_div_iff₀ hKR).mp (min_le_left _ _)
    calc
      (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]
        norm_num
      _ ≤ Real.exp ((K : ℝ) * (-s)) := Real.exp_le_exp.mpr (by nlinarith only [hbound])
      _ = Real.exp (-s) ^ K := Real.exp_nat_mul _ _
  · rw [Real.log_exp, neg_neg]
    exact min_le_right _ _

theorem norm_vandermonde_le_exp_of_fourier_mode {K d : ℕ} (hK : 0 < K) (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (z : Fin d → ℂ) (hz : ∀ i, ‖z i‖ = 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (hrK : (1 / 2 : ℝ) ≤ r ^ K)
    (hrlog : -Real.log r ≤ a ^ 2 / (2 * (K : ℝ)))
    (hsize : 8 * (K : ℝ) * (-Real.log (1 - r)) / a ^ 2 ≤ (d : ℝ))
    {m : ℕ} (hm : 0 < m) (hmK : m ≤ K) (hmode : a * (d : ℝ) ≤ ‖∑ i, z i ^ m‖) :
    ‖(Matrix.vandermonde z).det‖ ≤ Real.exp (-a ^ 2 * (d : ℝ) ^ 2 / (16 * (K : ℝ))) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hpow : (1 / 2 : ℝ) ≤ r ^ m :=
    hrK.trans (pow_le_pow_of_le_one hr.le hr1.le hmK)
  have hcoef : (1 / 2 : ℝ) / (K : ℝ) ≤ r ^ m / (m : ℝ) :=
    (div_le_div_of_nonneg_left (by norm_num) hmR (Nat.cast_le.mpr hmK)).trans
      (div_le_div_of_nonneg_right hpow hmR.le)
  have hsq : (a * (d : ℝ)) ^ 2 ≤ ‖∑ i, z i ^ m‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hmode
  have henergy : a ^ 2 * (d : ℝ) ^ 2 / (2 * (K : ℝ)) ≤
      r ^ m / (m : ℝ) * ‖∑ i, z i ^ m‖ ^ 2 := by
    calc
      _ = ((1 / 2 : ℝ) / (K : ℝ)) * (a * (d : ℝ)) ^ 2 := by
        field_simp
      _ ≤ _ := mul_le_mul hcoef hsq (sq_nonneg _) (by positivity)
  have hlogr : 0 ≤ -Real.log r := neg_nonneg.mpr (Real.log_nonpos hr.le hr1.le)
  have hpair : -(d : ℝ) * ((d : ℝ) - 1) * Real.log r / 4 ≤
      a ^ 2 * (d : ℝ) ^ 2 / (8 * (K : ℝ)) := by
    calc
      _ = ((d : ℝ) * ((d : ℝ) - 1)) * (-Real.log r) / 4 := by ring
      _ ≤ (d : ℝ) ^ 2 * (-Real.log r) / 4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (by nlinarith only [hdR] : (d : ℝ) * ((d : ℝ) - 1) ≤ (d : ℝ) ^ 2) hlogr)
          (by norm_num)
      _ ≤ (d : ℝ) ^ 2 * (a ^ 2 / (2 * (K : ℝ))) / 4 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrlog (sq_nonneg _))
          (by norm_num)
      _ = _ := by
        field_simp
        ring
  have hmul := mul_le_mul_of_nonneg_left
    ((div_le_iff₀ (sq_pos_of_pos ha)).mp hsize) hdR.le
  have hdiag : -(d : ℝ) * Real.log (1 - r) / 2 ≤
      a ^ 2 * (d : ℝ) ^ 2 / (16 * (K : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (K : ℝ))).mpr
    nlinarith only [hmul]
  refine (norm_vandermonde_le_regularized_energy z hz hr hr1 m).trans
    (Real.exp_le_exp.mpr ?_)
  simp only [div_eq_mul_inv, mul_inv_rev] at henergy hpair hdiag ⊢
  norm_num1 at henergy hpair hdiag ⊢
  nlinarith only [henergy, hpair, hdiag]

theorem exists_vandermonde_damping_of_fourier_mode {K : ℕ} (hK : 0 < K)
    {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∀ z : Fin d → ℂ,
      (∀ i, ‖z i‖ = 1) →
      (∃ m : ℕ, 0 < m ∧ m ≤ K ∧ a * (d : ℝ) ≤ ‖∑ i, z i ^ m‖) →
      ‖(Matrix.vandermonde z).det‖ < Real.exp (-c * (d : ℝ) ^ 2) := by
  obtain ⟨r, hr, hr1, hrK, hrlog⟩ := exists_regularized_circle_radius hK ha
  obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (8 * (K : ℝ) * (-Real.log (1 - r)) / a ^ 2))
  refine ⟨a ^ 2 / (32 * (K : ℝ)), by positivity, N, ?_⟩
  intro d hd z hz hmode
  have hNd : (N : ℝ) ≤ d := Nat.cast_le.mpr hd
  have hdR : (0 : ℝ) < d := (lt_of_le_of_lt (le_max_left _ _) hN).trans_le hNd
  have hsize : 8 * (K : ℝ) * (-Real.log (1 - r)) / a ^ 2 ≤ (d : ℝ) :=
    ((le_max_right _ _).trans hN.le).trans hNd
  obtain ⟨m, hm, hmK, hmode⟩ := hmode
  have hbound := norm_vandermonde_le_exp_of_fourier_mode hK
    (Nat.cast_pos.mp hdR) ha z hz hr hr1 hrK hrlog hsize hm hmK hmode
  refine hbound.trans_lt (Real.exp_lt_exp.mpr ?_)
  have hc : 0 < (a ^ 2 / (32 * (K : ℝ))) * (d : ℝ) ^ 2 := by positivity
  have heq : -a ^ 2 * (d : ℝ) ^ 2 / (16 * (K : ℝ)) =
      -2 * ((a ^ 2 / (32 * (K : ℝ))) * (d : ℝ) ^ 2) := by
    field_simp
    ring
  rw [heq]
  nlinarith only [hc]

end DirichletL
