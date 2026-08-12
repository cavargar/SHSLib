/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Eq. (24) of Bect (2010): Assumption 14 as an equality of measures on `E × E`

Assumption 14 requires the reset kernel `K` to admit a dual kernel `K*` with respect to
the volume measure `m`,

  `m(dx) K(x, dy) = m(dy) K*(y, dx)`.       (24)

In `SHSLib.FPK.SpontaneousJumps` this is stated in the integrated form
`GSHS.IsDualKernel`, as an identity between double integrals of an arbitrary
nonnegative jointly measurable test function.  This file shows that this integrated
form is *exactly* Eq. (24) read as an equality of measures on `E × E`: the composition
product `m ⊗ₘ K` (which is `m(dx)K(x, dy)`) coincides with the image of `m ⊗ₘ K*`
(which is `m(dy)K*(y, dx)`) under the coordinate swap.
-/
import SHSLib.FPK.SpontaneousJumps

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace GSHS

variable {E : Type*} [MeasurableSpace E]

/-- **Eq. (24)** (Assumption 14).  The dual-kernel condition `GSHS.IsDualKernel`, stated
as an identity of double integrals, is equivalent to the equality of measures on
`E × E`

  `m(dx) K(x, dy) = m(dy) K*(y, dx)`,

i.e. `m ⊗ₘ K = (m ⊗ₘ K*) ∘ swap⁻¹`. -/
theorem isDualKernel_iff_compProd_eq_map_swap (m : Measure E) [SFinite m]
    (K Kstar : Kernel E E) [IsSFiniteKernel K] [IsSFiniteKernel Kstar] :
    IsDualKernel m K Kstar ↔ m.compProd K = (m.compProd Kstar).map Prod.swap := by
  have key : ∀ f : E → E → ℝ≥0∞, Measurable (Function.uncurry f) →
      (∫⁻ x, (∫⁻ y, f x y ∂(K x)) ∂m = ∫⁻ p, Function.uncurry f p ∂(m.compProd K) ∧
       ∫⁻ y, (∫⁻ x, f x y ∂(Kstar y)) ∂m
          = ∫⁻ p, Function.uncurry f p ∂((m.compProd Kstar).map Prod.swap)) := by
    intro f hf
    refine ⟨(Measure.lintegral_compProd hf).symm, ?_⟩
    rw [lintegral_map hf measurable_swap,
      Measure.lintegral_compProd (f := fun a : E × E => Function.uncurry f a.swap)
        (hf.comp measurable_swap)]
    rfl
  constructor
  · intro h
    refine Measure.ext fun s hs => ?_
    obtain ⟨hL, hR⟩ := key (fun x y => s.indicator (fun _ => (1 : ℝ≥0∞)) (x, y))
      (measurable_one.indicator hs)
    have hone : ∀ μ : Measure (E × E),
        ∫⁻ p, Function.uncurry (fun x y => s.indicator (fun _ => (1 : ℝ≥0∞)) (x, y)) p ∂μ
          = μ s := by
      intro μ
      have huc : (Function.uncurry fun x y : E => s.indicator (fun _ => (1 : ℝ≥0∞)) (x, y))
          = s.indicator (fun _ => (1 : ℝ≥0∞)) := by funext p; cases p; rfl
      rw [huc, lintegral_indicator hs]
      simp
    rw [hone] at hL hR
    rw [← hL, ← hR]
    exact h _ (measurable_one.indicator hs)
  · intro h f hf
    obtain ⟨hL, hR⟩ := key f hf
    rw [hL, hR, h]

end GSHS
