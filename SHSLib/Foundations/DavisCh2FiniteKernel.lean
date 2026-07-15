import SHSLib.Foundations.DavisCh2

open MeasureTheory MeasurableSpace Topology Filter
open ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace Davis

/-!
# Finite-state transition kernel for the Davis renewal semigroup

This module supplies the next interface needed by the resolvent development.
On a finite measurable state space, the values of the positive normalized
linear operator `pdpSemigroup` on singleton indicators determine a Markov
transition kernel.
-/

/-- The finite-state transition kernel associated with `pdpSemigroup`.
Its mass at `y` is `Pₜ 1_{\{y\}}(x)`. -/
noncomputable def pdpSemigroupKernelFinite
    {E : Type*} [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]
    (p : PDP E) (t : ℝ≥0) : Kernel E E := by
  classical
  exact Kernel.ofFunOfCountable fun x =>
    ∑ y : E, ENNReal.ofReal
      (pdpSemigroup p t (fun z => if z = y then 1 else 0) x) • Measure.dirac y

/-
Finite functions decompose into singleton indicators, and the linearity of
`pdpSemigroup` carries this decomposition through the semigroup.
-/
lemma pdpSemigroup_eq_sum_singletons
    {E : Type*} [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]
    [DecidableEq E]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (t : ℝ≥0) (x : E) (g : E → ℝ) :
    pdpSemigroup pdp.toPDP t g x =
      ∑ y : E, g y * pdpSemigroup pdp.toPDP t
        (fun z => if z = y then 1 else 0) x := by
  have h_decomp : g = ∑ y, (fun z => g y * (if z = y then 1 else 0)) := by
    ext z; simp +decide [Finset.sum_apply] ;
  have h_linear : ∀ (f g : E → ℝ), pdpSemigroup pdp.toPDP t (f + g) x = pdpSemigroup pdp.toPDP t f x + pdpSemigroup pdp.toPDP t g x := by
    intro f g;
    apply_rules [ pdpSemigroup_add ];
    · fun_prop;
    · exact ⟨ ∑ x, |f x|, fun x => Finset.single_le_sum ( fun x _ => abs_nonneg ( f x ) ) ( Finset.mem_univ x ) ⟩;
    · grind +suggestions;
    · exact ⟨ ∑ x, |g x|, fun x => Finset.single_le_sum ( fun x _ => abs_nonneg ( g x ) ) ( Finset.mem_univ x ) ⟩;
  have h_linear : ∀ (f : E → ℝ) (a : ℝ), pdpSemigroup pdp.toPDP t (fun z => a * f z) x = a * pdpSemigroup pdp.toPDP t f x := by
    intro f a
    have h_linear : ∀ (f : E → ℝ) (a : ℝ), pdpSemigroup pdp.toPDP t (fun z => a * f z) x = a * pdpSemigroup pdp.toPDP t f x := by
      intro f a
      have h_measurable : Measurable f := by
        fun_prop
      have h_bounded : ∃ C : ℝ, ∀ x, |f x| ≤ C := by
        exact ⟨ ∑ x, |f x|, fun x => Finset.single_le_sum ( fun x _ => abs_nonneg ( f x ) ) ( Finset.mem_univ x ) ⟩
      convert pdpSemigroup_smul pdp a f h_measurable h_bounded hflow c hrate hcont t x using 1;
    exact h_linear f a;
  conv_lhs => rw [ h_decomp ];
  induction' ( Finset.univ : Finset E ) using Finset.induction <;> simp +decide [ ← h_linear ] at *;
  · simpa using ‹∀ f g : E → ℝ, pdpSemigroup pdp.toPDP t ( f + g ) x = pdpSemigroup pdp.toPDP t f x + pdpSemigroup pdp.toPDP t g x› 0 0;
  · grind +qlia

/-
On a finite measurable state space, `pdpSemigroupKernelFinite` is Markov
and represents the renewal-defined semigroup on every real-valued function.
-/
theorem pdpSemigroupKernelFinite_markov_and_integral
    {E : Type*} [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (t : ℝ≥0) :
    IsMarkovKernel (pdpSemigroupKernelFinite pdp.toPDP t) ∧
      ∀ (x : E) (g : E → ℝ),
        pdpSemigroup pdp.toPDP t g x =
          ∫ y, g y ∂(pdpSemigroupKernelFinite pdp.toPDP t x) := by
  refine' ⟨ ⟨ _ ⟩, _ ⟩;
  · intro x
    unfold pdpSemigroupKernelFinite
    simp [Kernel.ofFunOfCountable];
    constructor;
    convert pdpSemigroup_eq_sum_singletons pdp hflow c hrate hcont t x ( fun _ => 1 ) using 1;
    all_goals try exact Classical.decEq E;
    simp +decide;
    rw [ ← ENNReal.ofReal_sum_of_nonneg ];
    · rw [ ENNReal.ofReal_eq_one ];
      rw [ pdpSemigroup_const ];
      exacts [ eq_comm, hflow, c, hrate, hcont ];
    · intro y _;
      apply_rules [ pdpSemigroup_nonneg ];
      · exact Measurable.ite ( MeasurableSet.singleton y ) measurable_const measurable_const;
      · exact ⟨ 1, fun x => by split_ifs <;> norm_num ⟩;
      · exact fun _ => by split_ifs <;> norm_num;
  · intro x g; rw [ pdpSemigroupKernelFinite ] ; simp +decide [ Kernel.ofFunOfCountable ] ;
    rw [ MeasureTheory.integral_finset_sum_measure ] <;> norm_num [ MeasureTheory.integral_smul_measure ];
    · convert pdpSemigroup_eq_sum_singletons pdp hflow c hrate hcont t x g using 1;
      congr! 1;
      rw [ mul_comm, ENNReal.toReal_ofReal ];
      apply_rules [ pdpSemigroup_nonneg ];
      · exact Measurable.ite ( MeasurableSet.singleton _ ) measurable_const measurable_const;
      · exact ⟨ 1, fun x => by split_ifs <;> norm_num ⟩;
      · exact fun _ => by split_ifs <;> norm_num;
    · intro y; exact (by
      simp +decide [ MeasureTheory.Integrable, MeasureTheory.HasFiniteIntegral ];
      exact ⟨ Measurable.aestronglyMeasurable ( by measurability ), ENNReal.mul_lt_top ( ENNReal.ofReal_lt_top ) ( by simp +decide ) ⟩);

/-
On a finite standard state space, the renewal resolvent is α-excessive.
The transition-kernel hypothesis of `pdpResolvent_isAlphaExcessive_of_kernel`
is discharged by `pdpSemigroupKernelFinite`.
-/
theorem pdpResolvent_isAlphaExcessive_finite
    {E : Type*} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]
    [Fintype E] [MeasurableSingletonClass E]
    (pdp : PDPStandard E)
    (hrate_cont : Continuous (fun x => (pdp.jumpRate x : ℝ)))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (hflow_cont : Continuous (fun q : ℝ≥0 × E => pdp.flow q.1 q.2))
    (hcont : ∀ y, Continuous (fun s : ℝ =>
      (pdp.jumpRate (pdp.flow s.toNNReal y) : ℝ)))
    (hQ_cont : ∀ h : E → ℝ, Continuous h → (∃ D, ∀ x, |h x| ≤ D) →
      Continuous (fun x => ∫ y, h y ∂(pdp.transitionMeasure x)))
    {f : E → ℝ} (hf : Measurable f) (hf_cont : Continuous f)
    (hf_nonneg : ∀ y, 0 ≤ f y) (C : ℝ) (hfC : ∀ y, |f y| ≤ C)
    (alpha : ℝ≥0) (halpha : 0 < (alpha : ℝ)) :
    IsAlphaExcessive (pdpSemigroup pdp.toPDP) alpha
      (pdpResolvent pdp.toPDP alpha f) := by
  apply_rules [ pdpResolvent_isAlphaExcessive_of_kernel ];
  case K => exact fun t => pdpSemigroupKernelFinite pdp.toPDP t;
  · exact fun t => ( pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont t ).1;
  · intro t x g hg hg_bdd
    have := pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont t
    exact this.2 x g

end Davis