import Analysis.LocalAdjointInfinity
import Analysis.PolynomialOrders
import Analysis.ZagierODEPolynomials

/-!
The growth bound at infinity in CDT v2, proof of Lemma `14functions`,
equation `explicitode` and the fifth local expansion before `b3eq`.
The displayed ODE gives the indicial coefficient `-(s-3)^2*(s-4)^2`;
the differing printed coefficient gives the same bound on integer exponents.
-/

namespace DirichletL

open Polynomial Filter
open scoped Topology

private theorem coeff_degree_bound (i : Fin 5) :
    (zagierODECoeff i).natDegree ≤ i.val + 5 := by
  fin_cases i <;> norm_num [zagierODECoeff, Matrix.cons_val_two, zagierSingularCubic] <;>
    compute_degree!

private theorem coeff_top (i : Fin 5) :
    (zagierODECoeff i).coeff (i.val + 5) = ![0, 41472, 145152, 82944, 10368] i := by
  fin_cases i
  all_goals
    conv_lhs => arg 1; simp [zagierODECoeff, Matrix.cons_val_two, zagierSingularCubic]; ring_nf
    norm_num [coeff_add, coeff_mul_C, coeff_X, coeff_one]

private theorem regularization_infinity :
    ∃ U : Fin 4 → ℂ → ℂ, (∀ i, AnalyticAt ℂ (U i) 0) ∧
      (fun i => U i 0) = ![0, 4, 14, 8] ∧
      ∀ i : Fin 4, (fun z => (zagierODECoeff i.castSucc).eval z⁻¹ /
        (zagierODECoeff 4).eval z⁻¹) =ᶠ[𝓝[≠] 0]
          fun z => z ^ (4 - (i : ℤ)) * U i z := by
  let e := (zagierODECoeff 4).reflect 9
  let q (i : Fin 4) := (zagierODECoeff i.castSucc).reflect (i.val + 5)
  have he0 : e.eval 0 = 10368 := by
    simpa [e, ← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero] using coeff_top 4
  have he : e.eval 0 ≠ 0 := by rw [he0]; norm_num
  let U : Fin 4 → ℂ → ℂ := fun i z => (q i).eval z / e.eval z
  refine ⟨U, ?_, ?_, ?_⟩
  · intro i
    exact ((AnalyticOnNhd.eval_polynomial (q i)) 0 (Set.mem_univ 0)).div
      ((AnalyticOnNhd.eval_polynomial e) 0 (Set.mem_univ 0)) he
  · funext i
    have hq : (q i).eval 0 = ![0, 41472, 145152, 82944, 10368] i.castSucc := by
      simpa [q, ← coeff_zero_eq_eval_zero, coeff_reflect, revAt_zero] using coeff_top i.castSucc
    change (q i).eval 0 / e.eval 0 = _
    rw [hq, he0]
    fin_cases i <;> norm_num
  · intro i
    have hne := e.continuous.continuousAt.eventually_ne he
    filter_upwards [hne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hez hz
    change z ≠ 0 at hz
    rw [eval_inv_eq_reflect _ _ (coeff_degree_bound i.castSucc) hz,
      eval_inv_eq_reflect _ _ (coeff_degree_bound 4) hz]
    change (q i).eval z * (z⁻¹) ^ (i.val + 5) / (e.eval z * (z⁻¹) ^ 9) =
      z ^ (4 - (i : ℤ)) * ((q i).eval z / e.eval z)
    have hi : 4 - (i : ℤ) = ((4 - i.val : ℕ) : ℤ) := by have := i.isLt; omega
    rw [hi, zpow_natCast]
    have hp : z ^ (4 - i.val) * z ^ (i.val + 5) = z ^ 9 := by
      rw [← pow_add]
      congr 1
      have := i.isLt
      omega
    simp only [inv_pow]
    field_simp [hez, hz]
    linear_combination -(q i).eval z * hp

theorem adjointIndicial_infinity (s : ℂ) :
    adjointIndicial ![0, 4, 14, 8] s = -(s - 3) ^ 2 * (s - 4) ^ 2 := by
  simp [adjointIndicial]
  ring

theorem neg_four_le_order_zagierAdjointSystem_infinity
    (F : Fin 4 → ℂ → ℂ) (a b c : ℂ) (hF : MeromorphicAt (fun z => F 3 z⁻¹) 0)
    (hdiff : ∀ i, ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (F i) z⁻¹)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      deriv (F i.succ) z⁻¹ = (zagierODECoeff i.succ.castSucc).eval z⁻¹ /
        (zagierODECoeff 4).eval z⁻¹ * F 3 z⁻¹ - F i.castSucc z⁻¹)
    (hzero : (fun z => deriv (F 0) z⁻¹ - (zagierODECoeff 0).eval z⁻¹ /
      (zagierODECoeff 4).eval z⁻¹ * F 3 z⁻¹) =ᶠ[𝓝[≠] 0]
        fun z => a + b / z⁻¹ + c / (z⁻¹) ^ 2) :
    (-4 : WithTop ℤ) ≤ meromorphicOrderAt (fun z => F 3 z⁻¹) 0 := by
  rcases eq_or_ne (meromorphicOrderAt (fun z => F 3 z⁻¹) 0) ⊤ with htop | hfin
  · simp [htop]
  obtain ⟨M, hM⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hM]
  by_contra! hlt
  have hlt' : M < -4 := WithTop.coe_lt_coe.mp hlt
  obtain ⟨g, hg, hg0, h3⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hM.symm
  obtain ⟨U, hU, hU0, hA⟩ := regularization_infinity
  let G : Fin 4 → ℂ → ℂ := fun i z => F i z⁻¹
  let A : Fin 4 → ℂ → ℂ := fun i z =>
    (zagierODECoeff i.castSucc).eval z⁻¹ / (zagierODECoeff 4).eval z⁻¹
  have hd (i : Fin 4) : (fun z => -(z ^ 2) * deriv (G i) z) =ᶠ[𝓝[≠] 0]
      fun z => deriv (F i) z⁻¹ := by
    filter_upwards [hdiff i, self_mem_nhdsWithin] with z hdz hz
    exact neg_sq_mul_deriv_comp_inv hz hdz
  have hrec' : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] 0,
      -(z ^ 2) * deriv (G i.succ) z = A i.succ z * G 3 z - G i.castSucc z := by
    intro i
    filter_upwards [hd i.succ, hrec i] with z hdz hrec
    exact hdz.trans hrec
  have hzero' : (fun z => -(z ^ 2) * deriv (G 0) z - A 0 z * G 3 z) =ᶠ[𝓝[≠] 0]
      fun z => a + b * z + c * z ^ 2 := by
    filter_upwards [hd 0, hzero] with z hdz hz
    change -(z ^ 2) * deriv (G 0) z -
      (zagierODECoeff 0).eval z⁻¹ / (zagierODECoeff 4).eval z⁻¹ * F 3 z⁻¹ = _
    rw [hdz, hz]
    simp [div_eq_mul_inv]
  have he := adjointIndicial_neg_eq_zero_of_analytic M hg hg0 hU hA
    (by simpa [G, smul_eq_mul] using h3) hrec'
    ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).add
      (analyticAt_const.mul (analyticAt_id.pow 2))) hzero' hlt'
  rw [hU0, adjointIndicial_infinity] at he
  norm_num [mul_eq_zero, sub_eq_zero] at he
  norm_cast at he
  omega

end DirichletL
