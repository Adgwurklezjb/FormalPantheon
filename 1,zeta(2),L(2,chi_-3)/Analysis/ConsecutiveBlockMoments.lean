import Analysis.ConsecutiveBlocks

/-!
Exact first moments for CDT v2, supplied TeX 3998-4028.
-/

namespace DirichletL

theorem sum_consecutiveBlock_val_succ {s d : ℕ} (c : Fin (s + 1) → ℕ) (q : Fin s)
    (hc : c q.castSucc ≤ c q.succ) (hcd : c q.succ ≤ d) :
    2 * (∑ i ∈ consecutiveBlock (d := d) c q, ((i.val : ℝ) + 1)) =
      (c q.succ : ℝ) * ((c q.succ : ℝ) + 1) -
        (c q.castSucc : ℝ) * ((c q.castSucc : ℝ) + 1) := by
  have hsum : (∑ i ∈ consecutiveBlock (d := d) c q, ((i.val : ℝ) + 1)) =
      ∑ k ∈ Finset.Ico (c q.castSucc) (c q.succ), ((k : ℝ) + 1) := by
    apply Finset.sum_bij (fun i _ => i.val)
    · intro i hi
      simpa only [Finset.mem_Ico, mem_consecutiveBlock] using hi
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro k hk
      have hkd : k < d := (Finset.mem_Ico.mp hk).2.trans_le hcd
      refine ⟨⟨k, hkd⟩, ?_, rfl⟩
      simpa only [mem_consecutiveBlock, Finset.mem_Ico] using hk
    · intro i _
      rfl
  let F (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 1)
  rw [hsum]
  calc
    _ = ∑ k ∈ Finset.Ico (c q.castSucc) (c q.succ), (F (k + 1) - F k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [F]
      push_cast
      ring
    _ = _ := by simpa only [F] using Finset.sum_Ico_sub F hc

theorem normalized_cut_moment_bounds {d c : ℕ} (hd : 0 < d) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hcut : (c : ℝ) ≤ x * d ∧ x * d ≤ (c : ℝ) + 1) :
    -(2 / (d : ℝ)) ≤ (c : ℝ) * ((c : ℝ) + 1) / (d : ℝ) ^ 2 - x ^ 2 ∧
      (c : ℝ) * ((c : ℝ) + 1) / (d : ℝ) ^ 2 - x ^ 2 ≤ 1 / (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  let u : ℝ := (c : ℝ) / d
  have hu0 : 0 ≤ u := div_nonneg (Nat.cast_nonneg _) hdR.le
  have hux : u ≤ x := (div_le_iff₀ hdR).mpr hcut.1
  have hxupper : x ≤ u + 1 / (d : ℝ) := by
    change x ≤ (c : ℝ) / d + 1 / (d : ℝ)
    rw [← add_div]
    exact (le_div_iff₀ hdR).mpr hcut.2
  have hdelta : x - u ≤ 1 / (d : ℝ) := by linarith only [hxupper]
  have hproduct : (x - u) * (x + u) ≤ 2 / (d : ℝ) := by
    calc
      _ ≤ (1 / (d : ℝ)) * 2 :=
        mul_le_mul hdelta (by linarith only [hux, hx1]) (add_nonneg hx0 hu0)
          (one_div_nonneg.mpr hdR.le)
      _ = _ := by ring
  have hsquare : 0 ≤ (x - u) * (x + u) :=
    mul_nonneg (sub_nonneg.mpr hux) (add_nonneg hx0 hu0)
  have hover0 : 0 ≤ u / (d : ℝ) := div_nonneg hu0 hdR.le
  have hover1 : u / (d : ℝ) ≤ 1 / (d : ℝ) :=
    div_le_div_of_nonneg_right (hux.trans hx1) hdR.le
  have hform : (c : ℝ) * ((c : ℝ) + 1) / (d : ℝ) ^ 2 - x ^ 2 =
      u ^ 2 + u / (d : ℝ) - x ^ 2 := by
    dsimp only [u]
    field_simp [hdR.ne']
  rw [hform]
  constructor <;> nlinarith only [hproduct, hsquare, hover0, hover1]

end DirichletL
