/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Section 4.2 of Bect (2010): the "physical" interpretation of the jump term

The jump term of the generalized FPK equation (14) is `r_t (K - I) = r_t^src - r_t`,
the difference of the *source* term `r_t^src = r_t K` and the *sink* term `r_t`.
Bect's Section 4.2 observes that

* the total masses agree, `r_t(E) = r_t^src(E)`, so that the jump term conserves the
  total probability mass, and
* introducing the joint measure `W_t(dx, dy) = r_t(dx) K(x, dy)` on `E × E`, the sink is
  the first marginal of `W_t` and the source is the second one, so that Eq. (14) can be
  written in the symmetric form (17)

  `μ'_t = L^* μ_t + ∫ (W_t(dx, ·) - W_t(·, dx))`.

This file formalizes these statements: `GSHS.jumpFlow` is `W_t`, `GSHS.jumpFlow_fst`
and `GSHS.jumpFlow_snd` identify its marginals with the sink and the source, and
`GSHS.source_total_eq_sink_total` is the mass conservation identity.
-/
import SHSLib.FPK.SpontaneousJumps

open MeasureTheory Set ProbabilityTheory

noncomputable section

namespace GSHS

variable {E : Type*} [MeasurableSpace E]

/-- The joint jump flow `W_t(dx, dy) = r_t(dx) K(x, dy)` of Section 4.2: the mean
intensity of jumps from `dx` to `dy`. -/
def jumpFlow (r : Measure E) (K : Kernel E E) : Measure (E × E) := r ⊗ₘ K

/-- The pre-jump marginal of the jump flow is the sink term `r_t`. -/
theorem jumpFlow_fst (r : Measure E) [SFinite r] (K : Kernel E E) [IsMarkovKernel K] :
    (jumpFlow r K).fst = r :=
  Measure.fst_compProd r K

/-- The post-jump marginal of the jump flow is the source term `r_t^src = r_t K`. -/
theorem jumpFlow_snd (r : Measure E) [SFinite r] (K : Kernel E E) [IsSFiniteKernel K] :
    (jumpFlow r K).snd = K ∘ₘ r :=
  Measure.snd_compProd r K

/-- The source term evaluated on a measurable set: `r_t^src(Γ) = ∫ K(x, Γ) r_t(dx)`. -/
theorem source_apply (r : Measure E) (K : Kernel E E) {Γ : Set E} (hΓ : MeasurableSet Γ) :
    (K ∘ₘ r) Γ = ∫⁻ x, K x Γ ∂r :=
  Measure.bind_apply hΓ (Kernel.aemeasurable _)

/-- **Mass conservation** (Section 4.2): the source and the sink of the generalized FPK
equation carry the same total mass, `r_t(E) = r_t^src(E)`, because `K` is Markov. -/
theorem source_total_eq_sink_total (r : Measure E) (K : Kernel E E) [IsMarkovKernel K] :
    (K ∘ₘ r) univ = r univ := by
  rw [source_apply r K MeasurableSet.univ]
  simp

/-- **Eq. (17)**: the jump term of the generalized FPK equation is the difference of the
two marginals of the joint jump flow `W_t`, i.e.
`r_t^src(Γ) - r_t(Γ) = W_t(E × Γ) - W_t(Γ × E)`. -/
theorem jumpFlow_marginals (r : Measure E) [SFinite r] (K : Kernel E E) [IsMarkovKernel K]
    {Γ : Set E} (hΓ : MeasurableSet Γ) :
    jumpFlow r K (univ ×ˢ Γ) = (K ∘ₘ r) Γ ∧ jumpFlow r K (Γ ×ˢ univ) = r Γ := by
  have hs : ((univ : Set E) ×ˢ Γ) = Prod.snd ⁻¹' Γ := by ext z; simp
  have hf : (Γ ×ˢ (univ : Set E)) = Prod.fst ⁻¹' Γ := by ext z; simp
  refine ⟨?_, ?_⟩
  · rw [hs, ← Measure.snd_apply hΓ, jumpFlow_snd]
  · rw [hf, ← Measure.fst_apply hΓ, jumpFlow_fst]

end GSHS
