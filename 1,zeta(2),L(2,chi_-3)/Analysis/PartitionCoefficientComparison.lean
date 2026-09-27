import Analysis.SeededPartitionWeights
import Analysis.SeededVandermondeCoefficient

/-!
The same coefficient's signed derivative weights, CDT v2 TeX 3998-4028
and 4130-4228. Meanings precede this body in
-/

namespace DirichletL

theorem partition_weighted_log_norm_le_of_coeff_bounds {s d L : ℕ} {R ε : ℝ}
    (hs : 0 < s) (hd : 0 < d) (hR : 0 < R) (n : Fin d → ℕ)
    (σ : Equiv.Perm (Fin d)) (hmono : Monotone (fun i => n (σ i)))
    (hdis : HasIntervalDiscrepancyLE (fun i => (n i : ℝ) / R) ε)
    (hn : ∀ i, n i < L) (hLR : (L : ℝ) ≤ R + 1)
    (a : Fin (s + 1) → ℝ) (ha : Monotone a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1) (b : Fin d → Fin s)
    (hb : ∀ i q, b i = q ↔ a q.castSucc * d ≤ (i.val : ℝ) + 1 ∧
      ((i.val : ℝ) + 1 < a q.succ * d ∨ q.succ = Fin.last s))
    (β : ℚ) (hβ : β ≠ 0) (u : Fin s → ℂ) (hu : ∀ q, u q ≠ 0)
    (γ : ℂ) (hγ : γ = (β : ℂ) * ∏ i, u (b i) ^ n (σ i)) (A B : ℝ)
    (hlower : -Real.log |(β : ℝ)| ≤ A) (hupper : ‖γ‖ ≤ Real.exp B)
    {K : ℝ} (hK : ∀ q, |Real.log ‖u q‖| ≤ K) :
    (∑ q, (a q.succ ^ 2 - a q.castSucc ^ 2) * Real.log ‖u q‖) ≤
      2 * (A + B) / (R * (d : ℝ)) + 2 * ε * K + 3 * (s : ℝ) * K / d := by
  have hcoeff := sum_log_norm_le_of_coeff_bounds β hβ (fun i => u (b i))
    (fun i => hu (b i)) (fun i => n (σ i)) γ hγ A B hlower hupper
  have hweights := abs_seeded_partition_weight_sum_sub_le hs hd hR n σ hmono hdis hn hLR
    a ha ha0 ha1 b hb (fun q => Real.log ‖u q‖) hK
  have hscaled : (2 / (R * (d : ℝ))) * (∑ i, (n (σ i) : ℝ) * Real.log ‖u (b i)‖) ≤
      2 * (A + B) / (R * (d : ℝ)) := by
    calc
      _ ≤ (2 / (R * (d : ℝ))) * (A + B) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
      _ = _ := by ring
  have hlowerWeight := (abs_le.mp hweights).1
  linarith only [hlowerWeight, hscaled]

end DirichletL
