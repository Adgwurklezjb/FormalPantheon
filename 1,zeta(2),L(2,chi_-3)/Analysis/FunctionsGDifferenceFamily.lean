import Analysis.FunctionsGPrimitiveContinuation
import Analysis.ZagierPrimitiveIndependence

/-!
The seven differences of actual normalized G continuations in CDT v2,
Lemma `14functions` (supplied TeX 8083-8095), retaining all primitive
constants and the derivative order.
-/

namespace DirichletL

open Filter Set
open scoped Topology

theorem zagierODEState_sub {f g : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) :
    zagierODEState (f - g) z = zagierODEState f z - zagierODEState g z := by
  have hneg : -g = (-1 : ℂ) • g := by
    funext w
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul]
  rw [sub_eq_add_neg, zagierODEState_add hf hg.neg, hneg, zagierODEState_smul hg]
  simp only [neg_one_smul, sub_eq_add_neg]

theorem GPrimitiveContinuation.functions_sub_initial
    {δ : C(unitInterval, zagierPullbackRegularSet)} {k0 k1 : ℂ}
    (C : GPrimitiveContinuation δ k0 k1) (hδ : δ 1 = δ 0) {F : PowerSeries ℚ}
    (h0 : ∀ i : Fin 7, C.functions i 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
      zagierAuxiliaryFunctions F i) (i : Fin 7) :
    (C.functions i 1 - zagierAuxiliaryFunctions F i) =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))]
      zagierHomogeneousPrimitiveFamily (C.trace 1 - (complexSeries F).sum)
        (fun j => C.primitive j 1 - zagierAuxiliaryFunctions F (j.castAdd 4)) i := by
  have hG0 : C.trace 0 =ᶠ[𝓝 (mobiusCoordinate (δ 0 : ℂ))] (complexSeries F).sum := h0 3
  have hG : AnalyticAt ℂ (complexSeries F).sum (mobiusCoordinate (δ 0 : ℂ)) :=
    (C.trace_continuation.analytic 0).congr hG0
  have hC1 : AnalyticAt ℂ (C.trace 1) (mobiusCoordinate (δ 0 : ℂ)) := by
    simpa only [hδ] using C.trace_continuation.analytic 1
  have hstate : (fun z => zagierODEState (C.trace 1 - (complexSeries F).sum) z) =ᶠ[
      𝓝 (mobiusCoordinate (δ 0 : ℂ))]
      (fun z => zagierODEState (C.trace 1) z - zagierODEState (complexSeries F).sum z) := by
    filter_upwards [hC1.eventually_analyticAt, hG.eventually_analyticAt] with z hc hg
    exact zagierODEState_sub hc hg
  refine Fin.addCases (m := 3) (n := 4) ?_ ?_ i
  · intro j
    fin_cases j <;> exact Filter.EventuallyEq.rfl
  · intro j
    filter_upwards [hstate] with z hz
    have hj := congrFun hz j
    fin_cases j <;>
      simpa only [GPrimitiveContinuation.functions, zagierAuxiliaryFunctions,
        zagierHomogeneousPrimitiveFamily, Fin.append_right, zagierODEState,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.head_cons, Matrix.tail_cons, Pi.sub_apply] using hj.symm

end DirichletL
