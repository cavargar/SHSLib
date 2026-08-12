/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Section 6.1 of Bect (2010): models with spontaneous jumps only

For a GSHS without forced jumps (`G = ∅`), the mean jump intensity is
`r_t = λ μ_t` (Eq. (8)) and the source term of the generalized FPK equation is
`r_t^src = r_t K`.  **Assumption 14** postulates a dual kernel `K*` with

  `m(dx) K(x, dy) = m(dy) K*(y, dx)`,

and **Corollary 15** then states that, when `μ_t` has a density `p_t` with respect to
the volume measure `m`, both `r_t` and `r_t K` are absolutely continuous with

  `d r_t / dm = λ p_t`,   `d (r_t K) / dm = K*(λ p_t)`.   (25)

This file formalizes Assumption 14 (`GSHS.IsDualKernel`), the two density identities of
Corollary 15 (`GSHS.meanJumpIntensity_density`, `GSHS.corollary15_source_density`), and
the verification of Assumption 14 for an absolutely continuous reset kernel
`K(x, dy) = k(x, y) m(dy)` — Example 16, the case of the master equation (27).
-/
import SHSLib.FPK.MeanJumpIntensity

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

variable {E : Type*} [MeasurableSpace E]

/-- **Assumption 14** (Bect, 2010): the reset kernel `K` admits a dual kernel `K*` with
respect to the volume measure `m`, i.e. `m(dx) K(x, dy) = m(dy) K*(y, dx)`, expressed
as the equality of the two double integrals of an arbitrary nonnegative jointly
measurable test function. -/
def IsDualKernel (m : Measure E) (K Kstar : Kernel E E) : Prop :=
  ∀ f : E → E → ℝ≥0∞, Measurable (Function.uncurry f) →
    ∫⁻ x, (∫⁻ y, f x y ∂(K x)) ∂m = ∫⁻ y, (∫⁻ x, f x y ∂(Kstar y)) ∂m

/-- **Corollary 15, first identity of Eq. (25)**: if the law `μ_t` has density `p_t`
with respect to the volume measure `m`, then the mean jump intensity `r_t = λ μ_t`
(Eq. (8)) has density `λ p_t`. -/
theorem meanJumpIntensity_density {m : Measure E} {lam p : E → ℝ≥0∞}
    (hlam : Measurable lam) (hp : Measurable p) :
    (m.withDensity p).withDensity lam = m.withDensity (fun x => lam x * p x) := by
  rw [← withDensity_mul₀ hp.aemeasurable hlam.aemeasurable]
  congr 1
  funext x
  simp [mul_comm]

/-- **Corollary 15, second identity of Eq. (25)**: under Assumption 14, the source term
`r_t^src = r_t K` of the generalized FPK equation is absolutely continuous with respect
to the volume measure, with density `K*(λ p_t)`. -/
theorem corollary15_source_density {m : Measure E} {K Kstar : Kernel E E}
    (hdual : IsDualKernel m K Kstar) {lam p : E → ℝ≥0∞}
    (hlam : Measurable lam) (hp : Measurable p) {Γ : Set E} (hΓ : MeasurableSet Γ) :
    (K ∘ₘ (m.withDensity (fun x => lam x * p x))) Γ
      = ∫⁻ y in Γ, (∫⁻ x, lam x * p x ∂(Kstar y)) ∂m := by
  classical
  set g : E → ℝ≥0∞ := fun x => lam x * p x with hg
  have hgmeas : Measurable g := hlam.mul hp
  have h1 : (K ∘ₘ (m.withDensity g)) Γ = ∫⁻ x, K x Γ ∂(m.withDensity g) :=
    Measure.bind_apply hΓ (Kernel.aemeasurable _)
  have h2 : ∫⁻ x, K x Γ ∂(m.withDensity g) = ∫⁻ x, g x * K x Γ ∂m :=
    lintegral_withDensity_eq_lintegral_mul _ hgmeas (K.measurable_coe hΓ)
  -- rewrite `K x Γ` as an integral of the indicator against `K x`
  have h3 : ∀ x : E, g x * K x Γ = ∫⁻ y, Γ.indicator (fun _ => g x) y ∂(K x) := by
    intro x
    rw [lintegral_indicator hΓ, setLIntegral_const, mul_comm]
  have hfmeas : Measurable (Function.uncurry fun x y => Γ.indicator (fun _ => g x) y) := by
    have : (Function.uncurry fun x y => Γ.indicator (fun _ => g x) y)
        = fun q : E × E => (Γ.indicator (fun _ => (1 : ℝ≥0∞)) q.2) * g q.1 := by
      funext q
      by_cases hq : q.2 ∈ Γ
      · simp [Function.uncurry, indicator_of_mem hq]
      · simp [Function.uncurry, indicator_of_notMem hq]
    rw [this]
    exact ((measurable_one.indicator hΓ).comp measurable_snd).mul (hgmeas.comp measurable_fst)
  have h4 := hdual (fun x y => Γ.indicator (fun _ => g x) y) hfmeas
  rw [h1, h2]
  simp only [h3]
  rw [h4, ← lintegral_indicator hΓ]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ Γ
  · simp [indicator_of_mem hy]
  · simp [indicator_of_notMem hy]

/-- **Corollary 15, Eq. (25)** at the level of measures: under Assumption 14, the source
term `r_t^src = r_t K` of the generalized FPK equation is absolutely continuous with
respect to the volume measure `m`, with density `K*(λ p_t)`. -/
theorem corollary15_source_eq_withDensity {m : Measure E} {K Kstar : Kernel E E}
    (hdual : IsDualKernel m K Kstar) {lam p : E → ℝ≥0∞}
    (hlam : Measurable lam) (hp : Measurable p) :
    K ∘ₘ (m.withDensity fun x => lam x * p x)
      = m.withDensity fun y => ∫⁻ x, lam x * p x ∂(Kstar y) := by
  refine Measure.ext fun Γ hΓ => ?_
  rw [corollary15_source_density hdual hlam hp hΓ, withDensity_apply _ hΓ]

/-- **Example 16** (Bect, 2010): an absolutely continuous reset kernel
`K(x, dy) = k(x, y) m(dy)` satisfies Assumption 14, with dual kernel
`K*(y, dx) = k(x, y) m(dx)`.  This is the situation of the master equation (27). -/
theorem isDualKernel_of_density (m : Measure E) [SFinite m] {k : E → E → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) :
    IsDualKernel m (Kernel.withDensity (Kernel.const E m) fun x y => k x y)
      (Kernel.withDensity (Kernel.const E m) fun y x => k x y) := by
  intro f hf
  have hswap : Measurable (Function.uncurry fun y x => k x y) := by
    have : (Function.uncurry fun y x => k x y) = (Function.uncurry k) ∘ Prod.swap := by
      funext q; simp [Function.uncurry]
    rw [this]
    exact hk.comp measurable_swap
  have hleft : ∀ x : E,
      ∫⁻ y, f x y ∂((Kernel.withDensity (Kernel.const E m) fun x y => k x y) x)
        = ∫⁻ y, k x y * f x y ∂m := by
    intro x
    have hkx : Measurable (k x) := hk.comp measurable_prodMk_left
    have hfx : Measurable (fun y => f x y) := hf.comp measurable_prodMk_left
    rw [Kernel.withDensity_apply _ hk]
    simp only [Kernel.const_apply]
    rw [lintegral_withDensity_eq_lintegral_mul _ hkx hfx]
    rfl
  have hright : ∀ y : E,
      ∫⁻ x, f x y ∂((Kernel.withDensity (Kernel.const E m) fun y x => k x y) y)
        = ∫⁻ x, k x y * f x y ∂m := by
    intro y
    have hky : Measurable (fun x => k x y) := hswap.comp measurable_prodMk_left
    have hfy : Measurable (fun x => f x y) := by
      have : Measurable (Function.uncurry fun y x => f x y) := by
        have hswapf : (Function.uncurry fun y x => f x y)
            = (Function.uncurry f) ∘ Prod.swap := by
          funext q; simp [Function.uncurry]
        rw [hswapf]
        exact hf.comp measurable_swap
      exact this.comp measurable_prodMk_left
    rw [Kernel.withDensity_apply _ hswap]
    simp only [Kernel.const_apply]
    rw [lintegral_withDensity_eq_lintegral_mul _ hky hfy]
    rfl
  simp only [hleft, hright]
  have hprod : Measurable (Function.uncurry fun x y => k x y * f x y) := hk.mul hf
  exact lintegral_lintegral_swap hprod.aemeasurable

end GSHS
