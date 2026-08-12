/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Purely discrete modes: the forward Kolmogorov equation

Example 16 of Bect (2010) notes that, when all the modes of the hybrid system are purely
discrete (`n_q = 0`), the master equation (27) is "just the usual forward Kolmogorov
equation for a continuous-time Markov chain".  This file carries out that specialization:
the reference measure `m` is the counting measure on a finite state space `Q`, the reset
kernel has density `k` (a stochastic matrix) and the jump rate is
`γ(x, y) = λ(x) k(x, y)`.  On a finite state space every function is integrable and every
`m`-almost everywhere statement is an everywhere statement, so the conclusion of
`GSHS.master_equation_evolution` becomes the pointwise system of ordinary differential
equations

  `dp_y/dt = ∑ₓ (γ(x, y) p(x) − γ(y, x) p(y))`.   (27, discrete case)
-/
import SHSLib.FPK.MasterEquation

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace GSHS

variable {Q : Type*} [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]

omit [Fintype Q] [MeasurableSingletonClass Q] in
/-- On a space equipped with the counting measure, an almost-everywhere statement holds
everywhere. -/
theorem forall_of_ae_count {P : Q → Prop} (h : ∀ᵐ x ∂(Measure.count : Measure Q), P x) :
    ∀ x, P x := by
  have hzero : {x : Q | ¬ P x} = ∅ := Measure.count_eq_zero_iff.1 (by simpa [ae_iff] using h)
  intro x
  by_contra hx
  exact absurd (Set.eq_empty_iff_forall_notMem.1 hzero x) (by simp [hx])

/-- Every real function on a finite state space is integrable for the counting measure
restricted to any set. -/
theorem integrableOn_count_of_fintype (f : Q → ℝ) (s : Set Q) :
    IntegrableOn f s (Measure.count : Measure Q) :=
  (integrable_count_iff.2 (Summable.of_finite)).restrict

/-- **The forward Kolmogorov equation of a continuous-time Markov chain**, the purely
discrete case of the master equation (27) of Bect (2010).  On a finite state space `Q`
equipped with the counting measure, with reset probabilities `k` (a stochastic matrix),
jump intensity `λ` and jump rates `γ(x, y) = λ(x) k(x, y)`, the measure form of the
generalized FPK equation for a pure jump process forces, at *every* state `y`,

  `dp_y/dt = ∑ₓ γ(x, y) p(x) − ∑ₓ γ(y, x) p(y)`. -/
theorem kolmogorov_forward_equation {k : Q → Q → ℝ≥0∞} (hknorm : ∀ y, ∑ x, k y x = 1)
    (hk_top : ∀ x y, k x y ≠ ⊤) {lam p : Q → ℝ≥0∞} (hlam_top : ∀ x, lam x ≠ ⊤)
    (hp_top : ∀ x, p x ≠ ⊤) {dp : Q → ℝ}
    (hbal : ∀ s : Set Q, MeasurableSet s → (Measure.count : Measure Q) s < ⊤ →
      ∫ y in s, dp y ∂(Measure.count : Measure Q)
        = (((Kernel.withDensity (Kernel.const Q (Measure.count : Measure Q))
              fun x y => k x y) ∘ₘ
            ((Measure.count : Measure Q).withDensity fun x => lam x * p x)) s).toReal
          - (((Measure.count : Measure Q).withDensity fun x => lam x * p x) s).toReal) :
    ∀ y, dp y = (∑ x, (jumpRate lam k x y * p x).toReal)
      - ∑ x, (jumpRate lam k y x * p y).toReal := by
  have hjump_top : ∀ x y, jumpRate lam k x y * p x ≠ ⊤ := by
    intro x y
    simp only [jumpRate]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hlam_top x) (hk_top x y)) (hp_top x)
  -- the counting-measure integrals are finite sums
  have hsum : ∀ f : Q → ℝ≥0∞, ∫⁻ x, f x ∂(Measure.count : Measure Q) = ∑ x, f x := by
    intro f; rw [lintegral_count, tsum_fintype]
  have hnorm : ∀ y, ∫⁻ x, k y x ∂(Measure.count : Measure Q) = 1 := by
    intro y; rw [hsum]; exact hknorm y
  have hfin : ∀ (g : Q → ℝ≥0∞), (∀ x, g x ≠ ⊤) →
      (∫⁻ x, g x ∂(Measure.count : Measure Q)) < ⊤ := by
    intro g hg
    rw [hsum]
    exact ENNReal.sum_lt_top.2 fun x _ => lt_top_iff_ne_top.2 (hg x)
  have hae := master_equation_evolution (Measure.count : Measure Q)
    (measurable_of_countable _) hnorm (measurable_of_countable _) (measurable_of_countable _)
    (fun y => hfin _ fun x => hjump_top x y)
    (fun y => lt_top_iff_ne_top.2 (ENNReal.mul_ne_top (hlam_top y) (hp_top y)))
    (fun s _ _ => integrableOn_count_of_fintype dp s)
    (fun s _ _ => integrableOn_count_of_fintype _ s)
    (fun s _ _ => integrableOn_count_of_fintype _ s) hbal
  intro y
  have hy := forall_of_ae_count hae y
  rw [hy]
  beta_reduce
  rw [hsum, hsum, ENNReal.toReal_sum (fun x _ => hjump_top x y),
    ENNReal.toReal_sum (fun x _ => hjump_top y x)]

/-- The hypothesis of `GSHS.kolmogorov_forward_equation` is satisfiable: if the
derivative `dp` is *defined* by the right-hand side of the forward Kolmogorov equation,
then the measure form of the generalized FPK equation for a pure jump process holds on
every subset of the (finite) state space.  Together with
`GSHS.kolmogorov_forward_equation` this shows that the two formulations — the balance of
measures and the pointwise system of ODEs — are equivalent here. -/
theorem kolmogorov_forward_balance {k : Q → Q → ℝ≥0∞} (hknorm : ∀ y, ∑ x, k y x = 1)
    (hk_top : ∀ x y, k x y ≠ ⊤) {lam p : Q → ℝ≥0∞} (hlam_top : ∀ x, lam x ≠ ⊤)
    (hp_top : ∀ x, p x ≠ ⊤) (s : Set Q) :
    ∫ y in s, ((∑ x, (jumpRate lam k x y * p x).toReal)
        - ∑ x, (jumpRate lam k y x * p y).toReal) ∂(Measure.count : Measure Q)
      = (((Kernel.withDensity (Kernel.const Q (Measure.count : Measure Q))
            fun x y => k x y) ∘ₘ
          ((Measure.count : Measure Q).withDensity fun x => lam x * p x)) s).toReal
        - (((Measure.count : Measure Q).withDensity fun x => lam x * p x) s).toReal := by
  classical
  have hs : MeasurableSet s := MeasurableSet.of_discrete
  have hjump_top : ∀ x y, jumpRate lam k x y * p x ≠ ⊤ := by
    intro x y
    simp only [jumpRate]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (hlam_top x) (hk_top x y)) (hp_top x)
  set S : Q → ℝ≥0∞ := fun y => ∑ x, jumpRate lam k x y * p x with hS
  set T : Q → ℝ≥0∞ := fun y => lam y * p y with hT
  have hS_top : ∀ y, S y ≠ ⊤ := fun y =>
    (ENNReal.sum_lt_top.2 fun x _ => lt_top_iff_ne_top.2 (hjump_top x y)).ne
  have hT_top : ∀ y, T y ≠ ⊤ := fun y => ENNReal.mul_ne_top (hlam_top y) (hp_top y)
  -- the source measure, computed by Corollary 15 and the master equation source term
  have hsource : ((Kernel.withDensity (Kernel.const Q (Measure.count : Measure Q))
        fun x y => k x y) ∘ₘ
        ((Measure.count : Measure Q).withDensity fun x => lam x * p x))
      = (Measure.count : Measure Q).withDensity S := by
    rw [corollary15_source_eq_withDensity (isDualKernel_of_density _ (measurable_of_countable _))
      (measurable_of_countable lam) (measurable_of_countable p)]
    congr 1
    funext y
    rw [master_source (Measure.count : Measure Q) (measurable_of_countable _)
      (measurable_of_countable lam) (measurable_of_countable p) y, lintegral_count, tsum_fintype]
  -- both sides of the balance are finite sums of indicators
  have hwd : ∀ g : Q → ℝ≥0∞, ((Measure.count : Measure Q).withDensity g) s
      = ∑ y, s.indicator g y := by
    intro g
    rw [withDensity_apply _ hs, ← lintegral_indicator hs, lintegral_count, tsum_fintype]
  have hlhs : ∫ y in s, ((∑ x, (jumpRate lam k x y * p x).toReal)
        - ∑ x, (jumpRate lam k y x * p y).toReal) ∂(Measure.count : Measure Q)
      = ∑ y, s.indicator (fun y => (S y).toReal - (T y).toReal) y := by
    rw [← integral_indicator hs, integral_count]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      simp only [hS, hT]
      rw [ENNReal.toReal_sum (fun x _ => hjump_top x y),
        master_sink (Measure.count : Measure Q)
          (fun y => measurable_of_countable _)
          (fun y => by rw [lintegral_count, tsum_fintype]; exact hknorm y) lam p y,
        lintegral_count, tsum_fintype, ENNReal.toReal_sum (fun x _ => hjump_top y x)]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  rw [hlhs, hsource, hwd S, hwd T,
    ENNReal.toReal_sum (fun y _ => by
      by_cases hy : y ∈ s
      · rw [Set.indicator_of_mem hy]; exact hS_top y
      · rw [Set.indicator_of_notMem hy]; simp),
    ENNReal.toReal_sum (fun y _ => by
      by_cases hy : y ∈ s
      · rw [Set.indicator_of_mem hy]; exact hT_top y
      · rw [Set.indicator_of_notMem hy]; simp),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ s <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy]

end GSHS
