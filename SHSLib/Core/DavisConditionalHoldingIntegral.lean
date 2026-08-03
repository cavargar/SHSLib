import SHSLib.Core.DavisHazardDensity

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Conditional integration for Davis holding times

This module upgrades the event-level conditional survivor law to nonnegative
threshold-step tests.  Such tests are finite linear combinations of indicators
that the next holding time exceeds a deterministic threshold.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A nonnegative threshold-step test of the `k`-th holding time. -/
def davisHoldingThresholdStep {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (k : ℕ) {ι : Type*} (s : Finset ι) (u : ι → ℝ≥0)
    (w : ι → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  ∑ i ∈ s, w i * ({ω' | u i < ξ.holdingTime k ω'}.indicator (fun _ => (1 : ℝ≥0∞))) ω

/-- The conditional survivor law integrated against one weighted threshold
indicator. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.lintegral_weighted_survival_indicator
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) (u : ℝ≥0) (w : ℝ≥0∞) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    ∫⁻ ω in A, w * ({ω' | u < ξ.holdingTime k ω'}.indicator
        (fun _ => (1 : ℝ≥0∞))) ω ∂P =
      w * ∫⁻ ω in A, ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u) ∂P := by
  have hkey : ∫⁻ ω in A, ({ω' | u < ξ.holdingTime k ω'}.indicator (fun _ => (1 : ℝ≥0∞))) ω ∂P =
      ∫⁻ ω in A, ENNReal.ofReal ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow u) ∂P := by
    have hset : MeasurableSet {ω | u < ξ.holdingTime k ω} := by
      apply measurableSet_lt measurable_const (hξ.holdingTime k)
    rw [← hlaw.survivor_identity k u A hA]
    rw [MeasureTheory.lintegral_indicator hset]
    simp [Measure.restrict_apply hset, Set.inter_comm]
  have hmeas : Measurable ({ω' | u < ξ.holdingTime k ω'}.indicator (fun _ => (1 : ℝ≥0∞))) := by
    apply Measurable.indicator
    · exact measurable_const
    · exact measurableSet_lt measurable_const (hξ.holdingTime k)
  rw [lintegral_const_mul w hmeas, hkey]

/-- Finite nonnegative threshold-step tests integrate by replacing each
survival indicator with its history-dependent survivor factor. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.lintegral_thresholdStep
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) {ι : Type*} (s : Finset ι) (u : ι → ℝ≥0)
    (w : ι → ℝ≥0∞) (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    ∫⁻ ω in A, davisHoldingThresholdStep ξ k s u w ω ∂P =
      ∑ i ∈ s, w i * ∫⁻ ω in A, ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow (u i)) ∂P := by
  unfold davisHoldingThresholdStep
  rw [MeasureTheory.lintegral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact hlaw.lintegral_weighted_survival_indicator k (u i) (w i) A hA
  · intro i hi
    have hm : Measurable (fun ω : Ω =>
        ({ω' | u i < ξ.holdingTime k ω'}.indicator
          (fun _ => (1 : ℝ≥0∞))) ω) :=
      Measurable.indicator measurable_const
        ((hξ.holdingTime k) measurableSet_Ioi)
    exact hm.const_mul (w i)

end SHS
