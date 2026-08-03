import SHSLib.Core.DavisResetOccupationRegular

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Packaged holding-time threshold approximation data

This module packages the hypotheses of the monotone threshold approximation
theorem.  It is intended for the positive and negative variation pieces of a
stopped occupation integral; unlike the positive part of the final signed
integral, each variation piece is monotone in the holding time.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- A countable increasing threshold-step representation of a pair of
nonnegative functions: one depending on the sampled holding time and one on
its survivor transform. -/
structure DavisHoldingThresholdApproximationData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) (k : ℕ) (f g : Ω → ℝ≥0∞) where
  support : ℕ → Finset ℕ
  threshold : ℕ → ℕ → ℝ≥0
  weight : ℕ → ℕ → ℝ≥0∞
  survivorTerm_measurable : ∀ j i, i ∈ support j → Measurable (fun ω =>
    ENNReal.ofReal ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor
      S hflow (threshold j i)))
  sampled_monotone : Monotone (fun j =>
    davisHoldingThresholdStep ξ k (support j) (threshold j) (weight j))
  survivor_monotone : Monotone (fun j =>
    davisHoldingThresholdSurvivorStep S hflow ξ initial k
      (support j) (threshold j) (weight j))
  sampled_representation : ∀ ω, f ω = ⨆ j,
    davisHoldingThresholdStep ξ k (support j) (threshold j) (weight j) ω
  survivor_representation : ∀ ω, g ω = ⨆ j,
    davisHoldingThresholdSurvivorStep S hflow ξ initial k
      (support j) (threshold j) (weight j) ω

/-- The packaged approximation data directly yields the conditional
`lintegral` identity on every pre-jump-history event. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.lintegral_of_thresholdData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (k : ℕ) (f g : Ω → ℝ≥0∞)
    (hdata : DavisHoldingThresholdApproximationData (S := S) (hflow := hflow)
      (hf := hf) (hr := hr) hξ initial k f g)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A) :
    ∫⁻ ω in A, f ω ∂P = ∫⁻ ω in A, g ω ∂P := by
  simp_rw [hdata.sampled_representation, hdata.survivor_representation]
  apply hlaw.lintegral_iSup_thresholdStep k hdata.support hdata.threshold hdata.weight A hA
  · exact fun j i hi => hdata.survivorTerm_measurable j i hi
  · exact hdata.sampled_monotone
  · exact hdata.survivor_monotone

end SHS
