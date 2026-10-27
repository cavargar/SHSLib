/-
# The Markov property (Gardiner §4.3.2) for the Wiener process and geometric Brownian motion

* `condExp_freeze` (**freezing lemma**): if `Z` is `𝓖`-measurable, `Y` is independent of `𝓖` and
  `f` is bounded measurable, then `E[f(Z, Y) | 𝓖] = (z ↦ E f(z, Y))(Z)` almost surely.
* `wiener_markov`: `E[f(W(t)) | 𝓕 s] = (P_{s,t} f)(W(s))` a.s., where
  `P_{s,t} f(y) = E f(y + W(t) - W(s))` is the expectation at time `t` of `f` of the solution of
  `dx = dW` started at `y` at time `s` (`wienerTrans`); `wienerTrans_eq_gauss` identifies it with
  the Gaussian kernel `∫ f(y + z) N(0, t - s)(dz)`.
* `gbm_markov`: the same for geometric Brownian motion `X = geomBM λ μ x₀ W`, with
  `P_{s,t} f(y) = E f(y e^{(λ - μ²/2)(t - s) + μ (W(t) - W(s))})` (`gbmTrans`), the expectation of
  `f` at time `t` of the GBM started at `y` at time `s`.

The Markov property for general Lipschitz SDEs (needs a jointly measurable flow `y ↦ x^{s,y}`
measurable with respect to the increments of `W` after `s`) remains open; see the plan.
-/
import SHSLib.Gardiner.Ito.Generator.ExamplesGBM

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

noncomputable section

namespace Gardiner.Ito.Generator

open Gardiner.Ito

/-- **The freezing lemma**: for `Z` `𝓖`-measurable, `Y` independent of `𝓖` and `f` bounded
measurable, `E[f(Z, Y) | 𝓖] = g(Z)` a.s. with `g(z) = ∫ f(z, y) d(law of Y)(y)`. -/
theorem condExp_freeze {Ω : Type*} {𝓖 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (h𝓖 : 𝓖 ≤ mΩ) {Z Y : Ω → ℝ}
    (hZ : Measurable[𝓖] Z) (hY : Measurable Y)
    (hind : Indep (MeasurableSpace.comap Y inferInstance) 𝓖 P) {f : ℝ × ℝ → ℝ}
    (hf : Measurable f) {C : ℝ} (hfb : ∀ p, |f p| ≤ C) :
    P[fun ω => f (Z ω, Y ω) | 𝓖] =ᵐ[P] fun ω => ∫ y, f (Z ω, y) ∂(P.map Y) := by
  have hPY : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  set g : ℝ → ℝ := fun z => ∫ y, f (z, y) ∂(P.map Y) with hgdef
  have hg : StronglyMeasurable g := hf.stronglyMeasurable.integral_prod_right'
  have hZm : Measurable Z := hZ.mono h𝓖 le_rfl
  have hfi : Integrable (fun ω => f (Z ω, Y ω)) P :=
    Integrable.of_bound (hf.comp (hZm.prodMk hY)).aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hfb _)
  have hgb : ∀ z, |g z| ≤ C := fun z => by
    have := norm_integral_le_of_norm_le_const (μ := P.map Y) (f := fun y => f (z, y)) (C := C)
      (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hfb _)
    simpa using this
  have hgZ : Integrable (fun ω => g (Z ω)) P :=
    Integrable.of_bound (hg.measurable.comp hZm).aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hgb _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq h𝓖 hfi (fun s _ _ => hgZ.integrableOn)
    (fun A hA _ => ?_) (hg.comp_measurable hZ).aestronglyMeasurable).symm
  have hAm : MeasurableSet A := h𝓖 _ hA
  set ι : Ω → ℝ := A.indicator fun _ => (1 : ℝ) with hι
  have hιm : Measurable[𝓖] ι := measurable_const.indicator hA
  set X : Ω → ℝ × ℝ := fun ω => (ι ω, Z ω) with hXdef
  have hX : Measurable[𝓖] X := hιm.prodMk hZ
  have hXm : Measurable X := hX.mono h𝓖 le_rfl
  have hXY : IndepFun X Y P :=
    (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le_left hind.symm hX.comap_le)
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hY.aemeasurable).mp hXY
  set F : (ℝ × ℝ) × ℝ → ℝ := fun q => q.1.1 * f (q.1.2, q.2) with hF
  have hFm : Measurable F :=
    (measurable_fst.comp measurable_fst).mul
      (hf.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hιb : ∀ ω, |ι ω| ≤ 1 := fun ω => by
    by_cases h : ω ∈ A <;> simp [hι, h]
  have hPX : IsProbabilityMeasure (P.map X) := Measure.isProbabilityMeasure_map hXm.aemeasurable
  -- the right-hand side as an integral against the product law
  have hFi : Integrable F ((P.map X).prod (P.map Y)) := by
    rw [← hmap, integrable_map_measure hFm.aestronglyMeasurable
      (hXm.aemeasurable.prodMk hY.aemeasurable)]
    refine Integrable.of_bound (hFm.comp (hXm.prodMk hY)).aestronglyMeasurable C
      (ae_of_all _ fun ω => ?_)
    simp only [Function.comp, hF, hXdef, Real.norm_eq_abs, abs_mul]
    have h1 := hιb ω
    have h2 := hfb (Z ω, Y ω)
    have h3 : 0 ≤ |f (Z ω, Y ω)| := abs_nonneg _
    nlinarith [abs_nonneg (ι ω)]
  have e1 : ∫ ω in A, f (Z ω, Y ω) ∂P = ∫ ω, F (X ω, Y ω) ∂P := by
    rw [← integral_indicator hAm]
    congr 1; funext ω
    by_cases h : ω ∈ A <;> simp [hF, hXdef, hι, h]
  have e2 : ∫ ω in A, g (Z ω) ∂P = ∫ x, x.1 * g x.2 ∂(P.map X) := by
    have hmX := integral_map (μ := P) (φ := X) hXm.aemeasurable
      (f := fun x : ℝ × ℝ => x.1 * g x.2)
      (measurable_fst.mul (hg.measurable.comp measurable_snd)).aestronglyMeasurable
    rw [← integral_indicator hAm, hmX]
    congr 1; funext ω
    by_cases h : ω ∈ A <;> simp [hXdef, hι, h]
  have hmXY := integral_map (μ := P) (φ := fun ω => (X ω, Y ω))
    (hXm.aemeasurable.prodMk hY.aemeasurable) (f := F) hFm.aestronglyMeasurable
  rw [e1, e2, ← hmXY, hmap, integral_prod _ hFi]
  congr 1; funext x
  simp only [hF, hgdef]
  rw [integral_const_mul]

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ mΩ} {P : Measure Ω}
  {W : ℝ → Ω → ℝ} (hW : IsFWiener W 𝓕 P)
include hW

/-! ### The Wiener process -/

omit hW in
/-- The transition operator of `dx = dW`: `P_{s,t} f(y) = E f(y + W(t) - W(s))`, the expectation
of `f` at time `t` of the solution started at `y` at time `s`. -/
def wienerTrans (P : Measure Ω) (W : ℝ → Ω → ℝ) (s t : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ ω, f (y + (W t ω - W s ω)) ∂P

/-- `P_{s,t}` is the Gaussian kernel: `P_{s,t} f(y) = ∫ f(y + z) N(0, t - s)(dz)`. -/
lemma wienerTrans_eq_gauss {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {f : ℝ → ℝ} (hf : Measurable f)
    (y : ℝ) : wienerTrans P W s t f y = ∫ z, f (y + z) ∂(gaussianReal 0 (t - s).toNNReal) := by
  have h := integral_map (μ := P) (φ := W t - W s) (hW.measurable_incr s t).aemeasurable
    (f := fun z => f (y + z)) (hf.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  rw [wienerTrans, ← hW.law_sub s t hs hst, h]
  rfl

/-- **The Markov property of the Wiener process**: for bounded measurable `f` and `0 ≤ s ≤ t`,
`E[f(W(t)) | 𝓕 s] = (P_{s,t} f)(W(s))` almost surely. -/
theorem wiener_markov {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) {f : ℝ → ℝ} (hf : Measurable f)
    {C : ℝ} (hfb : ∀ y, |f y| ≤ C) :
    P[fun ω => f (W t ω) | 𝓕 s] =ᵐ[P] fun ω => wienerTrans P W s t f (W s ω) := by
  have := hW.isProbabilityMeasure
  have h := condExp_freeze (𝓖 := 𝓕 s) (𝓕.le s) (hW.adapted s hs).measurable
    (Y := W t - W s) (hW.measurable_incr s t) (hW.indep_past s t hs hst)
    (f := fun p => f (p.1 + p.2)) (hf.comp (measurable_fst.add measurable_snd)) (fun p => hfb _)
  have e : (fun ω => f (W t ω)) = fun ω => f (W s ω + (W t ω - W s ω)) := by
    funext ω; congr 1; ring
  rw [e]
  refine h.trans (Eventually.of_forall fun ω => ?_)
  have h2 := integral_map (μ := P) (φ := W t - W s) (hW.measurable_incr s t).aemeasurable
    (f := fun z => f (W s ω + z)) (hf.comp (measurable_const.add measurable_id)).aestronglyMeasurable
  simp only [wienerTrans]
  exact h2

/-! ### Geometric Brownian motion -/

omit hW in
/-- The transition operator of GBM: `P_{s,t} f(y) = E f(y e^{(λ - μ²/2)(t - s) + μ(W(t) - W(s))})`,
the expectation of `f` at time `t` of the GBM started at `y` at time `s`. -/
def gbmTrans (P : Measure Ω) (W : ℝ → Ω → ℝ) (lam mu s t : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ ω, f (y * exp ((lam - mu ^ 2 / 2) * (t - s) + mu * (W t ω - W s ω))) ∂P

/-- **The Markov property of geometric Brownian motion**: for an `𝓕 0`-measurable initial value,
bounded measurable `f` and `0 ≤ s ≤ t`, `E[f(X(t)) | 𝓕 s] = (P_{s,t} f)(X(s))` almost surely. -/
theorem gbm_markov (lam mu : ℝ) {x0 : Ω → ℝ} (hx0 : StronglyMeasurable[𝓕 0] x0) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hfb : ∀ y, |f y| ≤ C) :
    P[fun ω => f (geomBM lam mu x0 W t ω) | 𝓕 s] =ᵐ[P]
      fun ω => gbmTrans P W lam mu s t f (geomBM lam mu x0 W s ω) := by
  have := hW.isProbabilityMeasure
  set c := lam - mu ^ 2 / 2
  have hfun : Measurable fun p : ℝ × ℝ => f (p.1 * exp (c * (t - s) + mu * p.2)) :=
    hf.comp (measurable_fst.mul (Real.continuous_exp.measurable.comp
      (measurable_const.add (measurable_const.mul measurable_snd))))
  have h := condExp_freeze (𝓖 := 𝓕 s) (𝓕.le s) (hW.geomBM_sm (lam := lam) (mu := mu) hx0 hs).measurable
    (Y := W t - W s) (hW.measurable_incr s t) (hW.indep_past s t hs hst) hfun (fun p => hfb _)
  have e : (fun ω => f (geomBM lam mu x0 W t ω)) = fun ω =>
      f (geomBM lam mu x0 W s ω * exp (c * (t - s) + mu * (W t ω - W s ω))) := by
    funext ω
    congr 1
    simp only [geomBM, mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [e]
  refine h.trans (Eventually.of_forall fun ω => ?_)
  have h2 := integral_map (μ := P) (φ := W t - W s) (hW.measurable_incr s t).aemeasurable
    (f := fun z => f (geomBM lam mu x0 W s ω * exp (c * (t - s) + mu * z)))
    ((hfun.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  simp only [gbmTrans]
  exact h2

end Gardiner.Ito.Generator
