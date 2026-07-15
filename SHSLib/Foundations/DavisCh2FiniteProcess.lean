import SHSLib.Foundations.DavisCh2FiniteKernelSemigroup

open MeasureTheory MeasurableSpace Topology Filter
open ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace Davis

/-!
# Finite-state process interfaces for the renewal semigroup

This module connects the finite-state transition kernels constructed from
`pdpSemigroup` to conditional-expectation formulations of the Markov and strong
Markov properties.  The hypotheses below deliberately state the missing link
between an abstract process `X` and the PDP kernel; without such a link, the
corresponding process claims in the original Chapter 2 skeleton are false for
an arbitrary adapted process.
-/

/-
If a finite-state process has conditional transition law given by the
renewal kernel, then its conditional expectation is the renewal semigroup.
This is the finite-state, faithfully linked version of the simple Markov
interface in Davis (25.5).
-/
theorem pdp_simple_markov_finite_of_kernel
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [Fintype E] [MeasurableSingletonClass E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun u : ℝ =>
      (pdp.jumpRate (pdp.flow u.toNNReal y) : ℝ)))
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {f : E → ℝ} (t s : ℝ≥0)
    (hkernel :
      P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
        fun omega => ∫ y, f y
          ∂(pdpSemigroupKernelFinite pdp.toPDP s (X t omega))) :
    P[fun omega => f (X (t + s) omega) | ℱ t] =ᵐ[P]
      fun omega => pdpSemigroup pdp.toPDP s f (X t omega) := by
  refine' hkernel.trans _;
  filter_upwards [ ] with omega using Eq.symm ( by exact ( Davis.pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont s ).2 _ _ )

/-
The same kernel-to-semigroup bridge at a stopping time.  It isolates the
actual probabilistic strong-Markov input (`hkernel`) from the analytic fact
that the finite renewal kernel represents `pdpSemigroup`.
-/
theorem pdp_strong_markov_finite_of_kernel
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [Fintype E] [MeasurableSingletonClass E]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun u : ℝ =>
      (pdp.jumpRate (pdp.flow u.toNNReal y) : ℝ)))
    {X : ℝ≥0 → Omega → E}
    {ℱ : Filtration ℝ≥0 (‹MeasurableSpace Omega›)}
    {tau : Omega → ℝ≥0}
    (htau : IsStoppingTime ℱ (fun omega => (tau omega : ℝ≥0∞)))
    {f : E → ℝ} (s : ℝ≥0)
    (hkernel :
      P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
        fun omega => ∫ y, f y
          ∂(pdpSemigroupKernelFinite pdp.toPDP s (X (tau omega) omega))) :
    P[fun omega => f (X (tau omega + s) omega) | htau.measurableSpace] =ᵐ[P]
      fun omega => pdpSemigroup pdp.toPDP s f (X (tau omega) omega) := by
  refine' hkernel.trans _;
  filter_upwards [ ] with omega;
  convert ( pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont s ).2 ( X ( tau omega ) omega ) f |> Eq.symm

/-- Chapman--Kolmogorov in expectation form.  This is the tower-law
identity for a bounded observable, stated directly for the finite renewal
kernels. -/
theorem pdpSemigroupKernelFinite_integral_add
    {E : Type*} [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun u : ℝ =>
      (pdp.jumpRate (pdp.flow u.toNNReal y) : ℝ)))
    (s t : ℝ≥0) (x : E) (f : E → ℝ) :
    (∫ z, f z ∂(pdpSemigroupKernelFinite pdp.toPDP (s + t) x)) =
      ∫ y, (∫ z, f z ∂(pdpSemigroupKernelFinite pdp.toPDP t y))
        ∂(pdpSemigroupKernelFinite pdp.toPDP s x) := by
  have hf : Measurable f := by fun_prop
  have hb : ∃ C : ℝ, ∀ y, |f y| ≤ C :=
    ⟨∑ y : E, |f y|, fun y => Finset.single_le_sum
      (fun z _ => abs_nonneg (f z)) (Finset.mem_univ y)⟩
  rw [← (pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont
    (s + t)).2 x f]
  rw [pdpSemigroup_semigroup_property pdp f hf hb hflow c hrate hcont s t x]
  rw [(pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont s).2]
  congr 1
  funext y
  exact (pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont t).2 y f

end Davis
