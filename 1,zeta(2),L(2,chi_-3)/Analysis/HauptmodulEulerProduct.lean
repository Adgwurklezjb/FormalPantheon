import Analysis.FormalSeriesAlgebra

/-!
Exact denominator clearing for the formal Hauptmodul in CDT v2 Section 11.1,
equation `haupt`. All products here are coefficient-stabilized integer
power series; analytic evaluation is handled separately.
-/

namespace DirichletL

/-- The positive-index Euler product with formal argument X^d. -/
noncomputable def qEulerProductSeries (d : ℕ) : PowerSeries ℤ :=
  formalProduct (fun i => 1 - PowerSeries.X ^ (d * (i + 1)))

/-- The positive-index Euler product is normalized to have constant coefficient one. -/
theorem constantCoeff_qEulerProductSeries {d : ℕ} (hd : 0 < d) :
    PowerSeries.constantCoeff (R := ℤ) (qEulerProductSeries d) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, qEulerProductSeries,
    coeff_formalProduct, formalProductCoeff]
  simp [PowerSeries.coeff_X_pow, Nat.ne_of_gt hd]

theorem hauptmodul_mul_qEulerProductSeries :
    hauptmodul * qEulerProductSeries 2 ^ 8 * qEulerProductSeries 3 ^ 4 =
      PowerSeries.X * qEulerProductSeries 1 ^ 4 * qEulerProductSeries 6 ^ 8 := by
  let f (d i : ℕ) : PowerSeries ℤ := 1 - PowerSeries.X ^ (d * (i + 1))
  have hf (d : ℕ) (hd : 0 < d) (i : ℕ) : PowerSeries.X ^ (i + 1) ∣ f d i - 1 := by
    apply dvd_X_pow_sub_one_sub
    simpa only [one_mul] using Nat.mul_le_mul_right (i + 1) (show 1 ≤ d by omega)
  have hp (d : ℕ) (hd : 0 < d) (m i : ℕ) :
      PowerSeries.X ^ (i + 1) ∣ f d i ^ m - 1 :=
    dvd_pow_sub_one_of_dvd_sub_one (hf d hd i) m
  have hmul {a b d : PowerSeries ℤ} (ha : d ∣ a - 1) (hb : d ∣ b - 1) :
      d ∣ a * b - 1 := by
    convert dvd_add (dvd_mul_of_dvd_left ha b) hb using 1
    ring
  have hleft : formalProduct hauptFactor * qEulerProductSeries 2 ^ 8 *
      qEulerProductSeries 3 ^ 4 =
        formalProduct (fun i => hauptFactor i * f 2 i ^ 8 * f 3 i ^ 4) := by
    change formalProduct hauptFactor * formalProduct (f 2) ^ 8 *
      formalProduct (f 3) ^ 4 = _
    rw [formalProduct_pow (hf 2 (by norm_num)), formalProduct_pow (hf 3 (by norm_num)),
      formalProduct_mul dvd_hauptFactor_sub_one (hp 2 (by norm_num) 8),
      formalProduct_mul (fun i => hmul (dvd_hauptFactor_sub_one i) (hp 2 (by norm_num) 8 i))
        (hp 3 (by norm_num) 4)]
  have hright : qEulerProductSeries 1 ^ 4 * qEulerProductSeries 6 ^ 8 =
      formalProduct (fun i => f 1 i ^ 4 * f 6 i ^ 8) := by
    change formalProduct (f 1) ^ 4 * formalProduct (f 6) ^ 8 = _
    rw [formalProduct_pow (hf 1 (by norm_num)), formalProduct_pow (hf 6 (by norm_num)),
      formalProduct_mul (hp 1 (by norm_num) 4) (hp 6 (by norm_num) 8)]
  have hfactor (i : ℕ) : hauptFactor i * f 2 i ^ 8 * f 3 i ^ 4 =
      f 1 i ^ 4 * f 6 i ^ 8 := by
    have hcomm (a b c d u v : PowerSeries ℤ) :
        a ^ 4 * b ^ 8 * c ^ 8 * d ^ 4 * u ^ 8 * v ^ 4 =
          (a ^ 4 * b ^ 8) * (c * u) ^ 8 * (d * v) ^ 4 := by
      ring
    calc
      _ = (f 1 i ^ 4 * f 6 i ^ 8) *
          (oneSubInv (2 * (i + 1)) * f 2 i) ^ 8 *
          (oneSubInv (3 * (i + 1)) * f 3 i) ^ 4 := by
        simpa only [hauptFactor, f, one_mul] using
          hcomm (1 - PowerSeries.X ^ (i + 1)) (f 6 i)
            (oneSubInv (2 * (i + 1))) (oneSubInv (3 * (i + 1))) (f 2 i) (f 3 i)
      _ = _ := by
        rw [show oneSubInv (2 * (i + 1)) * f 2 i = 1 from
          oneSubInv_leftInv (by omega),
          show oneSubInv (3 * (i + 1)) * f 3 i = 1 from
          oneSubInv_leftInv (by omega), one_pow, one_pow, mul_one, mul_one]
  rw [hauptmodul]
  calc
    _ = PowerSeries.X * (formalProduct hauptFactor * qEulerProductSeries 2 ^ 8 *
        qEulerProductSeries 3 ^ 4) := by simp only [mul_assoc]
    _ = PowerSeries.X * formalProduct (fun i => f 1 i ^ 4 * f 6 i ^ 8) := by
      rw [hleft]
      exact congrArg (fun p : PowerSeries ℤ => PowerSeries.X * p)
        (congrArg formalProduct (funext hfactor))
    _ = _ := by rw [← hright, mul_assoc]

end DirichletL
