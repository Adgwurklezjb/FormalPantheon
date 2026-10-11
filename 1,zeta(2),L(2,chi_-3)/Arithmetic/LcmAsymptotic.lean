import Arithmetic.LcmGrowth
import Analysis.TauberianSqueeze

/-!
The sharp prefix-lcm asymptotic needed for CDT v2, Section 2.2,
supplied TeX 3291-3412. The weak PNT specialization follows the
PrimeNumberTheoremAnd contributors, Wiener.lean at revision
0766218b21b11ddf24103352ece7f0cb730945e0, lines 2230-2255, archived
-/

namespace DirichletL

open Filter Set
open scoped Topology ArithmeticFunction.vonMangoldt

theorem tendsto_sum_vonMangoldt_div :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, Λ n) / (N : ℝ)) atTop (𝓝 1) := by
  let G := ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hsum (N : ℕ) : (∑ n ∈ Finset.range N, ‖Λ n‖) ≤ (2 * Real.log 4) * N := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      using sum_vonMangoldt_le N
  have hf (σ : ℝ) (hσ : 1 < σ) :
      LSeriesSummable (fun n => (Λ n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hEq : EqOn G (fun s => LSeries (fun n => (Λ n : ℂ)) s - (1 : ℂ) / (s - 1))
      {s | 1 < s.re} := by
    intro s hs
    have he := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux
      (q := 1) (a := 1) isUnit_one hs
    calc
      G s = LSeries (fun n => (ArithmeticFunction.vonMangoldt.residueClass
          (1 : ZMod 1) n : ℂ)) s - (1 : ℂ) / (s - 1) := by
        simpa only [Nat.totient_one, Nat.cast_one, inv_one] using he
      _ = _ := by
        congr 1
        apply LSeries_congr
        intro n _
        have hc : (n : ZMod 1) = (1 : ZMod 1) := Subsingleton.elim _ _
        simp only [ArithmeticFunction.vonMangoldt.residueClass,
          Set.indicator_of_mem (show n ∈ {n : ℕ | (n : ZMod 1) = 1} from hc)]
  exact tendsto_sum_range_div_of_tauberian
    (fun _ => ArithmeticFunction.vonMangoldt_nonneg) (by norm_num) hsum hf
    (ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux 1) hEq

theorem tendsto_log_lcmPrefix_div :
    Tendsto (fun N : ℕ => Real.log (lcmPrefix N : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
  have hs := tendsto_sum_vonMangoldt_div.comp (tendsto_add_atTop_nat 1)
  have hi : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, one_div, add_zero] using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 (0 : ℝ))).const_add 1
  have ht := hs.mul hi
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hn' : (N : ℝ) + 1 ≠ 0 := by positivity
  dsimp only [Function.comp_def]
  rw [log_lcmPrefix_eq_sum_vonMangoldt]
  push_cast
  field_simp

end DirichletL
