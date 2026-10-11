import Analysis.PartitionExponentWeights

/-!
The retained sorted exponent in CDT v2, supplied TeX 3998-4028.
-/

namespace DirichletL

theorem abs_seeded_partition_weight_sum_sub_le {s d L : ℕ} {R ε : ℝ}
    (hs : 0 < s) (hd : 0 < d) (hR : 0 < R) (n : Fin d → ℕ)
    (σ : Equiv.Perm (Fin d)) (hmono : Monotone (fun i => n (σ i)))
    (hdis : HasIntervalDiscrepancyLE (fun i => (n i : ℝ) / R) ε)
    (hn : ∀ i, n i < L) (hLR : (L : ℝ) ≤ R + 1)
    (a : Fin (s + 1) → ℝ) (ha : Monotone a)
    (ha0 : a 0 = 0) (ha1 : a (Fin.last s) = 1) (b : Fin d → Fin s)
    (hb : ∀ i q, b i = q ↔ a q.castSucc * d ≤ (i.val : ℝ) + 1 ∧
      ((i.val : ℝ) + 1 < a q.succ * d ∨ q.succ = Fin.last s))
    (ℓ : Fin s → ℝ) {K : ℝ} (hK : ∀ q, |ℓ q| ≤ K) :
    |(2 / (R * (d : ℝ))) * (∑ i, (n (σ i) : ℝ) * ℓ (b i)) -
      ∑ q, (a q.succ ^ 2 - a q.castSucc ^ 2) * ℓ q| ≤
        2 * ε * K + 3 * (s : ℝ) * K / d := by
  let t (i : Fin d) : ℝ := (n (σ i) : ℝ) / R
  have hcube : ∀ i, t i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i => unit_interval_of_strict_nat_cutoff hR hLR n hn (σ i)
  have htmono : Monotone t := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ hR.le
    exact_mod_cast hmono hij
  have htdis : HasIntervalDiscrepancyLE t ε := hdis.comp_perm σ
  have h := htdis.abs_two_mul_sum_partition_weights_sub_le
    hcube htmono hs hd a ha ha0 ha1 b hb ℓ hK
  have hsum : (∑ i, t i * ℓ (b i)) = (∑ i, (n (σ i) : ℝ) * ℓ (b i)) / R := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [t]
    ring
  have hscale : 2 * (∑ i, t i * ℓ (b i)) / d =
      (2 / (R * (d : ℝ))) * (∑ i, (n (σ i) : ℝ) * ℓ (b i)) := by
    rw [hsum]
    ring
  rwa [hscale] at h

end DirichletL
