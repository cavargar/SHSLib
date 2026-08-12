/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Example 16 of Bect (2010): the master equation

For a pure jump process (`L = 0`) with an absolutely continuous reset kernel
`K(x, dy) = k(x, y) m(dy)`, Assumption 14 holds with `K*(y, dx) = k(x, y) m(dx)`
(this is `GSHS.isDualKernel_of_density` in `SHSLib/FPK/SpontaneousJumps.lean`).
Corollary 15 then gives the evolution equation `∂p_t/∂t = K*(λ p_t) − λ p_t`, whose two
terms are computed here in terms of the jump rate `γ(x, y) = λ(x) k(x, y)`:

* `GSHS.master_source` : `K*(λ p_t)(y) = ∫ γ(x, y) p_t(x) m(dx)`,
* `GSHS.master_sink`   : `λ(y) p_t(y) = ∫ γ(y, x) p_t(y) m(dx)`  (using that `K` is a
  Markov kernel, i.e. `∫ k(y, x) m(dx) = 1`),

which is exactly the master equation (27)

  `∂p/∂t (y, t) = ∫ (γ(x, y) p(x, t) − γ(y, x) p(y, t)) m(dx)`.
-/
import SHSLib.FPK.DensityEvolution

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GSHS

variable {E : Type*} [MeasurableSpace E]

/-- The jump rate `γ(x, y) = λ(x) k(x, y)` of the master equation (27). -/
def jumpRate (lam : E → ℝ≥0∞) (k : E → E → ℝ≥0∞) (x y : E) : ℝ≥0∞ := lam x * k x y

/-- **Source term of the master equation (27)**: the Corollary 15 source density
`K*(λ p_t)` of a pure jump process with reset density `k` equals
`∫ γ(x, y) p_t(x) m(dx)`. -/
theorem master_source (m : Measure E) [SFinite m] {k : E → E → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) {lam p : E → ℝ≥0∞}
    (hlam : Measurable lam) (hp : Measurable p) (y : E) :
    (∫⁻ x, lam x * p x
        ∂((Kernel.withDensity (Kernel.const E m) fun y x => k x y) y))
      = ∫⁻ x, jumpRate lam k x y * p x ∂m := by
  have hswap : Measurable (Function.uncurry fun y x => k x y) := by
    have : (Function.uncurry fun y x => k x y) = (Function.uncurry k) ∘ Prod.swap := by
      funext q; simp [Function.uncurry]
    rw [this]
    exact hk.comp measurable_swap
  have hky : Measurable fun x => k x y := hswap.comp measurable_prodMk_left
  rw [Kernel.withDensity_apply _ hswap]
  simp only [Kernel.const_apply]
  rw [lintegral_withDensity_eq_lintegral_mul _ hky (hlam.mul hp)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, jumpRate]
  ring

/-- **Sink term of the master equation (27)**: when `K` is a Markov kernel, i.e. when the
reset density `k` integrates to one, the sink density `λ p_t` can be written as
`∫ γ(y, x) p_t(y) m(dx)`. -/
theorem master_sink (m : Measure E) {k : E → E → ℝ≥0∞} (hk : ∀ y, Measurable (k y))
    (hnorm : ∀ y, ∫⁻ x, k y x ∂m = 1) (lam p : E → ℝ≥0∞) (y : E) :
    lam y * p y = ∫⁻ x, jumpRate lam k y x * p y ∂m := by
  have hrw : ∫⁻ x, jumpRate lam k y x * p y ∂m
      = ∫⁻ x, k y x * (lam y * p y) ∂m :=
    lintegral_congr fun x => by simp only [jumpRate]; ring
  rw [hrw, lintegral_mul_const _ (hk y), hnorm y, one_mul]

/-- Measurability of the source term `y ↦ ∫ γ(x, y) p(x) m(dx)` of the master
equation. -/
theorem measurable_masterSource (m : Measure E) [SFinite m] {k : E → E → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) {lam p : E → ℝ≥0∞}
    (hlam : Measurable lam) (hp : Measurable p) :
    Measurable fun y => ∫⁻ x, jumpRate lam k x y * p x ∂m := by
  have h : Measurable (Function.uncurry fun x y => jumpRate lam k x y * p x) := by
    have : (Function.uncurry fun x y => jumpRate lam k x y * p x)
        = fun q : E × E => (lam q.1 * k q.1 q.2) * p q.1 := by
      funext q; simp [Function.uncurry, jumpRate]
    rw [this]
    exact (((hlam.comp measurable_fst).mul hk).mul (hp.comp measurable_fst))
  exact h.lintegral_prod_left

/-- **The master equation (27)** (Example 16 of Bect, 2010).  For a pure jump process
(`L = 0`) with reset kernel `K(x, dy) = k(x, y) m(dy)` — which satisfies Assumption 14
by `GSHS.isDualKernel_of_density` — the generalized FPK equation in measure form,

  `μ'_t(Γ) = (r_t K)(Γ) − r_t(Γ)`,  with `r_t = λ p_t m`,

turns, `m`-almost everywhere, into the master equation

  `∂p/∂t (y, t) = ∫ (γ(x, y) p(x, t) − γ(y, x) p(y, t)) m(dx)`,   (27)

where `γ(x, y) = λ(x) k(x, y)` is the jump rate. -/
theorem master_equation_evolution (m : Measure E) [SigmaFinite m] {k : E → E → ℝ≥0∞}
    (hk : Measurable (Function.uncurry k)) (hnorm : ∀ y, ∫⁻ x, k y x ∂m = 1)
    {lam p : E → ℝ≥0∞} (hlam : Measurable lam) (hp : Measurable p) {dp : E → ℝ}
    (hsrc_lt_top : ∀ y, (∫⁻ x, jumpRate lam k x y * p x ∂m) < ⊤)
    (hsink_lt_top : ∀ y, lam y * p y < ⊤)
    (hdp : ∀ s, MeasurableSet s → m s < ⊤ → IntegrableOn dp s m)
    (hsrc : ∀ s, MeasurableSet s → m s < ⊤ →
      IntegrableOn (fun y => (∫⁻ x, jumpRate lam k x y * p x ∂m).toReal) s m)
    (hsink : ∀ s, MeasurableSet s → m s < ⊤ →
      IntegrableOn (fun y => (∫⁻ x, jumpRate lam k y x * p y ∂m).toReal) s m)
    (hbal : ∀ s, MeasurableSet s → m s < ⊤ →
      ∫ y in s, dp y ∂m
        = (((Kernel.withDensity (Kernel.const E m) fun x y => k x y) ∘ₘ
            (m.withDensity fun x => lam x * p x)) s).toReal
          - ((m.withDensity fun x => lam x * p x) s).toReal) :
    dp =ᵐ[m] fun y => (∫⁻ x, jumpRate lam k x y * p x ∂m).toReal
      - (∫⁻ x, jumpRate lam k y x * p y ∂m).toReal := by
  have hky : ∀ y, Measurable (k y) := fun y => hk.comp measurable_prodMk_left
  -- the two terms of the master equation, in the form produced by Corollary 15
  have hsrcpt := master_source m hk hlam hp
  have hsinkpt := master_sink m hky hnorm lam p
  have hsrcfun : (fun y => ∫⁻ x, lam x * p x
        ∂((Kernel.withDensity (Kernel.const E m) fun y x => k x y) y))
      = fun y => ∫⁻ x, jumpRate lam k x y * p x ∂m :=
    funext hsrcpt
  have hsrcfun' : (fun y => (∫⁻ x, lam x * p x
        ∂((Kernel.withDensity (Kernel.const E m) fun y x => k x y) y)).toReal)
      = fun y => (∫⁻ x, jumpRate lam k x y * p x ∂m).toReal :=
    funext fun y => by rw [hsrcpt y]
  have hsinkfun' : (fun y => (lam y * p y).toReal)
      = fun y => (∫⁻ x, jumpRate lam k y x * p y ∂m).toReal :=
    funext fun y => by rw [hsinkpt y]
  have hsrc_meas : Measurable fun y => ∫⁻ x, lam x * p x
      ∂((Kernel.withDensity (Kernel.const E m) fun y x => k x y) y) := by
    rw [hsrcfun]; exact measurable_masterSource m hk hlam hp
  have key := corollary15_pdf_evolution (dp := dp) (Fp := fun _ => (0 : ℝ)) m
    (isDualKernel_of_density m hk) hlam hp hsrc_meas
    (fun y => by rw [hsrcpt y]; exact hsrc_lt_top y) hsink_lt_top hdp
    (fun s _ _ => integrableOn_zero)
    (fun s hs hfin => by rw [hsrcfun']; exact hsrc s hs hfin)
    (fun s hs hfin => by rw [hsinkfun']; exact hsink s hs hfin)
    (fun s hs hfin => by simpa using hbal s hs hfin)
  refine key.trans (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [hsrcpt y, hsinkpt y, zero_add]

end GSHS
