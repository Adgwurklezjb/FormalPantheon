import Mathlib

/-!
Uniform initial-segment errors for the PNT interval argument in CDT v2,
Section 2.2, supplied TeX 3330-3359. Native little-o bounds control the
tail, and a finite sum absorbs the initial segment.
-/

namespace DirichletL

open Filter
open scoped Topology

theorem eventually_abs_initialSegment_le {u : ℕ → ℝ}
    (hu : Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m ≤ N, |u m| ≤ ε * (N : ℝ) := by
  have hzero : ∀ᶠ n : ℕ in atTop, (n : ℝ) = 0 → u n = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn hz
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    exact (hnR.ne' hz).elim
  have hlittle := (Asymptotics.isLittleO_iff_tendsto' hzero).mpr hu
  have htail : ∀ᶠ n : ℕ in atTop, |u n| ≤ ε * (n : ℝ) := by
    simpa only [Real.norm_eq_abs, Nat.abs_cast] using hlittle.bound hε
  obtain ⟨M, hM⟩ := eventually_atTop.mp htail
  let C : ℝ := ∑ m ∈ Finset.range M, |u m|
  filter_upwards [eventually_ge_atTop ⌈C / ε⌉₊] with N hN m hmN
  by_cases hm : m < M
  · have hmC : |u m| ≤ C :=
      Finset.single_le_sum (fun i _ => abs_nonneg (u i)) (Finset.mem_range.mpr hm)
    have hCN : C / ε ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    have hC : C ≤ ε * (N : ℝ) := by
      have h := (div_le_iff₀ hε).mp hCN
      nlinarith
    exact hmC.trans hC
  · exact (hM m (Nat.le_of_not_gt hm)).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hmN) hε.le)

theorem eventually_abs_initialSegment_sub_le {s : ℕ → ℝ} {A : ℝ}
    (hs : Tendsto (fun n : ℕ => s n / (n : ℝ)) atTop (𝓝 A)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m ≤ N, |s m - A * (m : ℝ)| ≤ ε * (N : ℝ) := by
  have ht : Tendsto (fun n : ℕ => s n / (n : ℝ) - A) atTop (𝓝 0) := by
    simpa only [sub_self] using hs.sub_const A
  have hu : Tendsto (fun n : ℕ => (s n - A * (n : ℝ)) / (n : ℝ)) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  exact eventually_abs_initialSegment_le hu hε

end DirichletL
