import SHSLib.Core.DavisHoldingSignedHistoryThresholdData

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Rectangular approximations for history-dependent holding occupations

A history/time rectangle contributes a history-event indicator multiplied by a
strict holding-time threshold indicator.  This file gives the approximation
object a density-oriented interface and converts it to the threshold data used
by the conditional holding-time theorem.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Increasing finite rectangular approximations of a nonnegative sampled
occupation and its survivor transform.  Each rectangle is specified by a
pre-jump-history event, an elapsed-time threshold, and a nonnegative weight. -/
structure DavisHoldingHistoryRectangularApproximationData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) (k : ℕ) (sampled survivor : Ω → ℝ≥0∞) where
  support : ℕ → Finset ℕ
  historyEvent : ℕ → ℕ → Set Ω
  elapsedThreshold : ℕ → ℕ → ℝ≥0
  rectangleWeight : ℕ → ℕ → ℝ≥0∞
  historyEvent_measurable : ∀ j i, i ∈ support j →
    MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (historyEvent j i)
  survivor_measurable : ∀ j i, i ∈ support j → Measurable (fun ω =>
    ENNReal.ofReal ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor
      S hflow (elapsedThreshold j i)))
  sampled_monotone : Monotone (fun j =>
    davisHoldingHistoryThresholdStep ξ k (support j) (historyEvent j)
      (elapsedThreshold j) (rectangleWeight j))
  survivor_monotone : Monotone (fun j =>
    davisHoldingHistoryThresholdSurvivorStep S hflow ξ initial k
      (support j) (historyEvent j) (elapsedThreshold j) (rectangleWeight j))
  sampled_eq_iSup_rectangles : ∀ ω, sampled ω = ⨆ j,
    davisHoldingHistoryThresholdStep ξ k (support j) (historyEvent j)
      (elapsedThreshold j) (rectangleWeight j) ω
  survivor_eq_iSup_rectangles : ∀ ω, survivor ω = ⨆ j,
    davisHoldingHistoryThresholdSurvivorStep S hflow ξ initial k
      (support j) (historyEvent j) (elapsedThreshold j) (rectangleWeight j) ω

/-- Rectangular occupation data supplies the packaged history-threshold data. -/
def DavisHoldingHistoryRectangularApproximationData.toThresholdData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n} {k : ℕ} {sampled survivor : Ω → ℝ≥0∞}
    (hrect : DavisHoldingHistoryRectangularApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr)
      hξ initial k sampled survivor) :
    DavisHoldingHistoryThresholdApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr)
      hξ initial k sampled survivor := by
  exact
    { support := hrect.support
      event := hrect.historyEvent
      threshold := hrect.elapsedThreshold
      weight := hrect.rectangleWeight
      event_measurable := hrect.historyEvent_measurable
      survivorTerm_measurable := hrect.survivor_measurable
      sampled_monotone := hrect.sampled_monotone
      survivor_monotone := hrect.survivor_monotone
      sampled_representation := hrect.sampled_eq_iSup_rectangles
      survivor_representation := hrect.survivor_eq_iSup_rectangles }

/-- Separate positive and negative rectangular approximations assemble into
signed history-threshold approximation data. -/
def davisSignedHistoryThresholdData_of_rectangles
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n} {k : ℕ} {f g : Ω → ℝ}
    (hpos : DavisHoldingHistoryRectangularApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
      (fun ω => ENNReal.ofReal (f ω)) (fun ω => ENNReal.ofReal (g ω)))
    (hneg : DavisHoldingHistoryRectangularApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
      (fun ω => ENNReal.ofReal (-f ω)) (fun ω => ENNReal.ofReal (-g ω))) :
    DavisHoldingSignedHistoryThresholdApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr)
      hξ initial k f g := by
  exact ⟨hpos.toThresholdData, hneg.toThresholdData⟩

end SHS
