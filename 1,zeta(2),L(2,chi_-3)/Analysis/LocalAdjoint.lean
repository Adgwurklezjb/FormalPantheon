import Analysis.LocalExpansions

/-!
The local backward calculation in CDT v2, proof of Lemma `14functions`,
equations after `remaining` and the expansions preceding `b3eq`.
-/

namespace DirichletL

open Filter
open scoped Topology

/-- Leading coefficient of the fourth-order backward adjoint residual. -/
def adjointIndicial (v : Fin 4 → ℂ) (s : ℂ) : ℂ :=
  (s - 3) * (v 1 - (s - 2) * (v 2 - (s - 1) * (v 3 - s))) - v 0

private theorem factor_mul {f g u v : ℂ → ℂ} {a : ℂ} {M N : ℤ}
    (hf : f =ᶠ[𝓝[≠] a] fun z => (z - a) ^ M * u z)
    (hg : g =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * v z) :
    (fun z => f z * g z) =ᶠ[𝓝[≠] a] fun z => (z - a) ^ (M + N) * (u z * v z) := by
  filter_upwards [hf, hg, self_mem_nhdsWithin] with z hfz hgz hza
  rw [hfz, hgz, zpow_add₀ (sub_ne_zero.mpr hza)]
  ring

private theorem backward_factor {f g v b : ℂ → ℂ} {a : ℂ} (M : ℤ)
    (hg : AnalyticAt ℂ g a) (hv : AnalyticAt ℂ v a)
    (hf : f =ᶠ[𝓝[≠] a] fun z => (z - a) ^ M * g z)
    (hb : b =ᶠ[𝓝[≠] a] fun z => (z - a) ^ (M - 1) * v z - deriv f z) :
    ∃ w : ℂ → ℂ, AnalyticAt ℂ w a ∧ w a = v a - (M : ℂ) * g a ∧
      b =ᶠ[𝓝[≠] a] fun z => (z - a) ^ (M - 1) * w z := by
  obtain ⟨u, hu, hua, hfu⟩ := exists_analytic_factor_deriv M hg hf
  refine ⟨fun z => v z - u z, hv.sub hu, by simpa using congrArg (v a - ·) hua, ?_⟩
  filter_upwards [hb, hfu] with z hbz hfz
  rw [hbz, hfz, mul_sub]

theorem exists_analytic_factor_adjointSystem {A U F : Fin 4 → ℂ → ℂ} {g : ℂ → ℂ}
    {a : ℂ} (N : ℤ) (hg : AnalyticAt ℂ g a) (hU : ∀ i, AnalyticAt ℂ (U i) a)
    (hA : ∀ i : Fin 4, A i =ᶠ[𝓝[≠] a] fun z => (z - a) ^ ((i : ℤ) - 4) * U i z)
    (h3 : F 3 =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * g z)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] a,
      deriv (F i.succ) z = A i.succ z * F 3 z - F i.castSucc z) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧
      r a = adjointIndicial (fun i => U i a) N * g a ∧
      (fun z => deriv (F 0) z - A 0 z * F 3 z) =ᶠ[𝓝[≠] a]
        fun z => (z - a) ^ (N - 4) * r z := by
  have hmul (i : Fin 4) := factor_mul (hA i) h3
  have step (i : Fin 3) (M : ℤ) (v : ℂ → ℂ) (hv : AnalyticAt ℂ v a)
      (hF : F i.succ =ᶠ[𝓝[≠] a] fun z => (z - a) ^ M * v z)
      (hM : M - 1 = ((i.succ : Fin 4) : ℤ) - 4 + N) :
      ∃ w : ℂ → ℂ, AnalyticAt ℂ w a ∧
        w a = U i.succ a * g a - (M : ℂ) * v a ∧
        F i.castSucc =ᶠ[𝓝[≠] a] fun z => (z - a) ^ (M - 1) * w z := by
    apply backward_factor M hv ((hU _).mul hg) hF
    filter_upwards [hrec i, hmul i.succ] with z hr hm
    rw [← hM] at hm
    change F i.castSucc z = (z - a) ^ (M - 1) * (U i.succ z * g z) - deriv (F i.succ) z
    linear_combination hm + hr
  obtain ⟨v2, hv2, he2, hF2⟩ := step 2 N g hg h3 (by norm_num; omega)
  obtain ⟨v1, hv1, he1, hF1⟩ := step 1 (N - 1) v2 hv2 hF2 (by norm_num; omega)
  obtain ⟨v0, hv0, he0, hF0⟩ := step 0 (N - 1 - 1) v1 hv1 hF1 (by norm_num; omega)
  obtain ⟨u, hu, hua, hdu⟩ := exists_analytic_factor_deriv (N - 1 - 1 - 1) hv0 hF0
  refine ⟨fun z => u z - U 0 z * g z, hu.sub ((hU 0).mul hg), ?_, ?_⟩
  · simp only [hua, he0, he1, he2, adjointIndicial]
    norm_num
    push_cast
    ring
  · filter_upwards [hdu, hmul 0] with z hd hm
    have hN : N - 1 - 1 - 1 - 1 = N - 4 := by omega
    have hN0 : ((0 : Fin 4) : ℤ) - 4 + N = N - 4 := by norm_num; omega
    rw [hN] at hd
    rw [hN0] at hm
    change deriv (F 0) z = _ at hd
    rw [hd, hm, mul_sub]

theorem adjointIndicial_eq_zero_of_analytic {A U F : Fin 4 → ℂ → ℂ} {g R : ℂ → ℂ}
    {a : ℂ} (N : ℤ) (hg : AnalyticAt ℂ g a) (hg0 : g a ≠ 0)
    (hU : ∀ i, AnalyticAt ℂ (U i) a)
    (hA : ∀ i : Fin 4, A i =ᶠ[𝓝[≠] a] fun z => (z - a) ^ ((i : ℤ) - 4) * U i z)
    (h3 : F 3 =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * g z)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] a,
      deriv (F i.succ) z = A i.succ z * F 3 z - F i.castSucc z)
    (hR : AnalyticAt ℂ R a)
    (hzero : (fun z => deriv (F 0) z - A 0 z * F 3 z) =ᶠ[𝓝[≠] a] R)
    (hN : N < 4) : adjointIndicial (fun i => U i a) N = 0 := by
  obtain ⟨r, hr, hra, hres⟩ := exists_analytic_factor_adjointSystem N hg hU hA h3 hrec
  have hr0 := eq_zero_of_analytic_zpow_mul_of_neg hR hr (hzero.symm.trans hres)
    (show N - 4 < 0 by omega)
  rw [hra] at hr0
  exact (mul_eq_zero.mp hr0).resolve_right hg0

theorem adjointIndicial_eq_zero_of_analytic_mul {A U F : Fin 4 → ℂ → ℂ} {g R : ℂ → ℂ}
    {a : ℂ} (N : ℤ) (k : ℕ) (hg : AnalyticAt ℂ g a) (hg0 : g a ≠ 0)
    (hU : ∀ i, AnalyticAt ℂ (U i) a)
    (hA : ∀ i : Fin 4, A i =ᶠ[𝓝[≠] a] fun z => (z - a) ^ ((i : ℤ) - 4) * U i z)
    (h3 : F 3 =ᶠ[𝓝[≠] a] fun z => (z - a) ^ N * g z)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] a,
      deriv (F i.succ) z = A i.succ z * F 3 z - F i.castSucc z)
    (hR : AnalyticAt ℂ R a)
    (hzero : (fun z => (z - a) ^ k * (deriv (F 0) z - A 0 z * F 3 z)) =ᶠ[𝓝[≠] a] R)
    (hN : N + k < 4) : adjointIndicial (fun i => U i a) N = 0 := by
  obtain ⟨r, hr, hra, hres⟩ := exists_analytic_factor_adjointSystem N hg hU hA h3 hrec
  have hRr : R =ᶠ[𝓝[≠] a] fun z => (z - a) ^ ((k : ℤ) + (N - 4)) * r z := by
    filter_upwards [hzero, hres, self_mem_nhdsWithin] with z hz hresz hza
    rw [← hz, hresz, zpow_add₀ (sub_ne_zero.mpr hza), zpow_natCast, mul_assoc]
  have hr0 := eq_zero_of_analytic_zpow_mul_of_neg hR hr hRr (by omega)
  rw [hra] at hr0
  exact (mul_eq_zero.mp hr0).resolve_right hg0

theorem exists_analytic_regularization_of_factorization (p q : Fin 4 → Polynomial ℂ)
    (d e : Polynomial ℂ) (a : ℂ) (m : ℕ)
    (hd : d = (Polynomial.X - Polynomial.C a) ^ m * e) (he : e.eval a ≠ 0)
    (hq : ∀ i : Fin 4, (Polynomial.X - Polynomial.C a) ^ (4 - i.val) * p i =
      (Polynomial.X - Polynomial.C a) ^ m * q i) :
    ∃ U : Fin 4 → ℂ → ℂ, (∀ i, AnalyticAt ℂ (U i) a) ∧
      (∀ i, U i a = (q i).eval a / e.eval a) ∧
      ∀ i : Fin 4, (fun z => (p i).eval z / d.eval z) =ᶠ[𝓝[≠] a]
        fun z => (z - a) ^ ((i : ℤ) - 4) * U i z := by
  refine ⟨fun i z => (q i).eval z / e.eval z, ?_, fun _ => rfl, ?_⟩
  · intro i
    exact ((AnalyticOnNhd.eval_polynomial (q i)) a (Set.mem_univ a)).div
      ((AnalyticOnNhd.eval_polynomial e) a (Set.mem_univ a)) he
  · intro i
    have he' := e.continuous.continuousAt.eventually_ne he
    filter_upwards [he'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hez hza
    have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
    have hc := congrArg (Polynomial.eval z) (hq i)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hc
    have hi : (i : ℤ) - 4 = -((4 - i.val : ℕ) : ℤ) := by have := i.isLt; omega
    rw [hd, hi, zpow_neg, zpow_natCast]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    field_simp [hez, hne]
    linear_combination hc

theorem exists_analytic_regularization_of_simple_root (p : Fin 4 → Polynomial ℂ)
    (d : Polynomial ℂ) (a : ℂ) (hd : d.eval a = 0) (hd' : d.derivative.eval a ≠ 0) :
    ∃ U : Fin 4 → ℂ → ℂ, (∀ i, AnalyticAt ℂ (U i) a) ∧
      (fun i => U i a) = ![0, 0, 0, (p 3).eval a / d.derivative.eval a] ∧
      ∀ i : Fin 4, (fun z => (p i).eval z / d.eval z) =ᶠ[𝓝[≠] a]
        fun z => (z - a) ^ ((i : ℤ) - 4) * U i z := by
  let T := d /ₘ (Polynomial.X - Polynomial.C a)
  have hT : T.eval a = d.derivative.eval a := by
    have h := congrArg (Polynomial.eval a)
      (Polynomial.divByMonic_add_X_sub_C_mul_derivate_divByMonic_eq_derivative d a)
    simpa using h
  have hT0 : T.eval a ≠ 0 := hT ▸ hd'
  have hdT : (Polynomial.X - Polynomial.C a) * T = d :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hd
  let U : Fin 4 → ℂ → ℂ := fun i z =>
    (z - a) ^ (3 - i.val) * ((p i).eval z / T.eval z)
  refine ⟨U, ?_, ?_, ?_⟩
  · intro i
    exact ((analyticAt_id.sub analyticAt_const).pow _).mul
      (((AnalyticOnNhd.eval_polynomial (p i)) a (Set.mem_univ a)).div
        ((AnalyticOnNhd.eval_polynomial T) a (Set.mem_univ a)) hT0)
  · funext i
    fin_cases i <;> simp [U, hT]
  · intro i
    have hTne := T.continuous.continuousAt.eventually_ne hT0
    filter_upwards [hTne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hTz hza
    have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
    have he := congrArg (Polynomial.eval z) hdT
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at he
    rw [← he]
    change (p i).eval z / ((z - a) * T.eval z) =
      (z - a) ^ ((i : ℤ) - 4) * ((z - a) ^ (3 - i.val) * ((p i).eval z / T.eval z))
    have hi : (i : ℤ) - 4 + ((3 - i.val : ℕ) : ℤ) = -1 := by
      have := i.isLt
      omega
    rw [← zpow_natCast (z - a) (3 - i.val), ← mul_assoc, ← zpow_add₀ hne, hi]
    simp only [zpow_neg_one, div_eq_mul_inv, mul_inv]
    ring

theorem le_order_adjointSystem_of_simple_root (p : Fin 4 → Polynomial ℂ)
    (d : Polynomial ℂ) (a : ℂ) (ρ : ℤ) (hd : d.eval a = 0) (hd' : d.derivative.eval a ≠ 0)
    (hρ : (p 3).eval a = (ρ : ℂ) * d.derivative.eval a)
    (F : Fin 4 → ℂ → ℂ) (R : ℂ → ℂ) (hF : MeromorphicAt (F 3) a)
    (hrec : ∀ i : Fin 3, ∀ᶠ z in 𝓝[≠] a,
      deriv (F i.succ) z = (p i.succ).eval z / d.eval z * F 3 z - F i.castSucc z)
    (hR : AnalyticAt ℂ R a)
    (hzero : (fun z => deriv (F 0) z - (p 0).eval z / d.eval z * F 3 z) =ᶠ[𝓝[≠] a] R) :
    (min 1 ρ : ℤ) ≤ meromorphicOrderAt (F 3) a := by
  rcases eq_or_ne (meromorphicOrderAt (F 3) a) ⊤ with htop | hfin
  · simp [htop]
  obtain ⟨N, hN⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hN]
  by_contra! hlt
  have hlt' : N < min 1 ρ := by exact_mod_cast hlt
  obtain ⟨g, hg, hg0, h3⟩ := (meromorphicOrderAt_eq_int_iff hF).mp hN.symm
  obtain ⟨U, hU, hUa, hA⟩ := exists_analytic_regularization_of_simple_root p d a hd hd'
  have hr : (p 3).eval a / d.derivative.eval a = (ρ : ℂ) := by
    rw [hρ, mul_div_cancel_right₀ _ hd']
  rw [hr] at hUa
  have he := adjointIndicial_eq_zero_of_analytic N hg hg0 hU hA
    (by simpa only [smul_eq_mul] using h3) hrec hR hzero (by omega)
  rw [hUa] at he
  have hpoly : adjointIndicial ![0, 0, 0, (ρ : ℂ)] N =
      -((N : ℂ) - 3) * ((N : ℂ) - 2) * ((N : ℂ) - 1) * ((N : ℂ) - ρ) := by
    simp [adjointIndicial]
    ring
  rw [hpoly] at he
  simp only [mul_eq_zero, neg_eq_zero, sub_eq_zero] at he
  norm_cast at he
  omega

end DirichletL
