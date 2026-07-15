import SHSLib.Foundations.DavisCh2FiniteKernel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory MeasurableSpace Topology Filter
open ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace Davis

/-!
# Semigroup laws for the finite-state renewal kernel

This module upgrades the finite-state representation of `pdpSemigroup` to a
transition-function interface.  The kernel at time zero is the identity kernel,
and kernel composition agrees with addition of elapsed times.
-/

/-
The finite-state transition kernel at time zero is the identity kernel.
-/
theorem pdpSemigroupKernelFinite_zero
    {E : Type*} [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]
    (p : PDP E) :
    pdpSemigroupKernelFinite p 0 = Kernel.id := by
  ext x s; simp +decide [ pdpSemigroupKernelFinite, Kernel.id_apply, pdpSemigroup_zero ] ;
  simp +decide [ Kernel.ofFunOfCountable, Set.indicator ];
  rw [ Finset.sum_eq_single x ] <;> aesop

/-
Chapman--Kolmogorov for the finite-state transition kernels:
`K_(s+t) = K_t ∘ K_s`, in the composition convention used by Mathlib.
-/
theorem pdpSemigroupKernelFinite_add
    {E : Type*} [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun u : ℝ =>
      (pdp.jumpRate (pdp.flow u.toNNReal y) : ℝ)))
    (s t : ℝ≥0) :
    pdpSemigroupKernelFinite pdp.toPDP (s + t) =
      (pdpSemigroupKernelFinite pdp.toPDP t).comp
        (pdpSemigroupKernelFinite pdp.toPDP s) := by
  convert pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont ( s + t ) |>.2 using 1;
  constructor <;> intro h <;> simp_all +decide [ Kernel.ext_iff ];
  · intro x g; rw [ ← h x ] ; exact ( pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont ( s + t ) ) |>.2 x g;
  · intro x
    have h_eq : ∀ (g : E → ℝ), ∫ y, g y ∂(pdpSemigroupKernelFinite pdp.toPDP (s + t)) x = ∫ y, (∫ z, g z ∂(pdpSemigroupKernelFinite pdp.toPDP t) y) ∂(pdpSemigroupKernelFinite pdp.toPDP s) x := by
      intro g
      have h_eq : pdpSemigroup pdp.toPDP (s + t) g x = pdpSemigroup pdp.toPDP s (fun y => pdpSemigroup pdp.toPDP t g y) x := by
        apply pdpSemigroup_semigroup_property pdp g (by
        grind +suggestions) (by
        exact ⟨ ∑ x, |g x|, fun x => Finset.single_le_sum ( fun x _ => abs_nonneg ( g x ) ) ( Finset.mem_univ x ) ⟩) hflow c hrate hcont s t x
      rw [h x g, h_eq] at *; (
      convert pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont s |>.2 x ( fun y => pdpSemigroup pdp.toPDP t g y ) using 1;
      exact congr_arg _ ( funext fun y => by rw [ pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont t |>.2 y g ] ));
    ext g;
    convert congr_arg ENNReal.ofReal ( h_eq ( fun y => if y ∈ g then 1 else 0 ) ) using 1;
    any_goals exact fun y => Classical.dec ( y ∈ g );
    · rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
      change ( pdpSemigroupKernelFinite pdp.toPDP ( s + t ) x ) g = ENNReal.ofReal ( ∫ y in g, 1 ∂ ( pdpSemigroupKernelFinite pdp.toPDP ( s + t ) x ) );
      · simp +decide [ MeasureTheory.measureReal_def ];
        rw [ ENNReal.ofReal_toReal ];
        have := pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont ( s + t );
        exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.subset_univ _ ) ) ( by simp +decide [ this.1.1 ] ) );
      · assumption;
      · norm_num [ Filter.EventuallyEq, Set.indicator ];
    · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
      · rw [ ENNReal.ofReal_toReal ];
        · rw [ ProbabilityTheory.Kernel.comp_apply' ];
          · congr! 2;
            rw [ MeasureTheory.integral_congr_ae, MeasureTheory.integral_indicator ];
            change ( pdpSemigroupKernelFinite pdp.toPDP t _ ) g = ENNReal.ofReal ( ∫ x in g, 1 ∂ ( pdpSemigroupKernelFinite pdp.toPDP t _ ) );
            · simp +decide [ MeasureTheory.measureReal_def ];
              rw [ ENNReal.ofReal_toReal ];
              simp +decide [ pdpSemigroupKernelFinite ];
              simp +decide [ Kernel.ofFunOfCountable ];
              intro x; by_cases hx : x ∈ g <;> simp +decide [ hx ] ;
            · assumption;
            · exact Filter.Eventually.of_forall fun x => by simp +decide [ Set.indicator ] ;
          · assumption;
        · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun y => _ ) _ );
          use fun y => 1;
          · rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
            · rw [ ENNReal.ofReal_toReal ];
              · refine' le_trans ( MeasureTheory.lintegral_mono fun x => _ ) _;
                use fun _ => 1;
                · split_ifs <;> norm_num;
                · have := pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont t;
                  have := this.1.1 y; aesop;
              · refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.lintegral_mono fun x => _ ) _ );
                use fun _ => 1;
                · split_ifs <;> norm_num;
                · simp +decide [ pdpSemigroupKernelFinite ];
                  simp +decide [ Kernel.ofFunOfCountable ];
            · exact Filter.Eventually.of_forall fun z => by positivity;
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.ite ‹_› measurable_const measurable_const );
          · simp +decide [ pdpSemigroupKernelFinite ];
            simp +decide [ Kernel.ofFunOfCountable ];
      · exact Filter.Eventually.of_forall fun y => MeasureTheory.integral_nonneg fun z => by positivity;
      · fun_prop

/-
The finite-state renewal kernels form a Markov transition function: every
kernel has total mass one, time zero is the identity, and elapsed times compose
according to Chapman--Kolmogorov.
-/
theorem pdpSemigroupKernelFinite_transitionFunction
    {E : Type*} [MeasurableSpace E] [Fintype E] [MeasurableSingletonClass E]
    (pdp : PDPStandard E)
    (hflow : Measurable (fun q : ℝ × E => pdp.flow q.1.toNNReal q.2))
    (c : ℝ≥0) (hrate : ∀ y, pdp.jumpRate y ≤ c)
    (hcont : ∀ y, Continuous (fun u : ℝ =>
      (pdp.jumpRate (pdp.flow u.toNNReal y) : ℝ))) :
    (∀ t, IsMarkovKernel (pdpSemigroupKernelFinite pdp.toPDP t)) ∧
    pdpSemigroupKernelFinite pdp.toPDP 0 = Kernel.id ∧
    ∀ s t, pdpSemigroupKernelFinite pdp.toPDP (s + t) =
      (pdpSemigroupKernelFinite pdp.toPDP t).comp
        (pdpSemigroupKernelFinite pdp.toPDP s) := by
  exact ⟨ fun t => ( pdpSemigroupKernelFinite_markov_and_integral pdp hflow c hrate hcont t ).1, by exact pdpSemigroupKernelFinite_zero pdp.toPDP, fun s t => by exact pdpSemigroupKernelFinite_add pdp hflow c hrate hcont s t ⟩

end Davis