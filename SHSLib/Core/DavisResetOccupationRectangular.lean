import SHSLib.Core.DavisHoldingHistoryRectangularApproximation
import SHSLib.Core.DavisResetOccupationIntegrable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Capped reset occupation from rectangular variation data

This is the concrete assembly point for the approximation and integrability
batches: positive and negative rectangular approximations of capped reset
occupation imply its conditional survivor-weighted compensator identity.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Positive and negative rectangular variation data, together with
integrability, imply the capped conditional reset-occupation identity. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.integral_cappedSampledResetOccupation_eq_expected_of_rectangles
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (g : DavisState Q n → ℝ) (k : ℕ) (u : ℝ≥0)
    (hpos : DavisHoldingHistoryRectangularApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
      (fun ω => ENNReal.ofReal
        (davisCappedSampledResetOccupationCompensator S hflow g ξ initial k u ω))
      (fun ω => ENNReal.ofReal
        (davisSegmentExpectedResetCompensator S hflow g
          (davisPreJumpHistory S hflow ξ initial k ω).currentState u)))
    (hneg : DavisHoldingHistoryRectangularApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
      (fun ω => ENNReal.ofReal
        (-davisCappedSampledResetOccupationCompensator S hflow g ξ initial k u ω))
      (fun ω => ENNReal.ofReal
        (-davisSegmentExpectedResetCompensator S hflow g
          (davisPreJumpHistory S hflow ξ initial k ω).currentState u)))
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hsampled : IntegrableOn
      (davisCappedSampledResetOccupationCompensator S hflow g ξ initial k u) A P)
    (hexpected : IntegrableOn (fun ω =>
      davisSegmentExpectedResetCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState u) A P) :
    ∫ ω in A, davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k u ω ∂P =
      ∫ ω in A, davisSegmentExpectedResetCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState u ∂P := by
  apply hlaw.integral_cappedSampledResetOccupation_eq_expected_of_historyData
    g k u (davisSignedHistoryThresholdData_of_rectangles hpos hneg)
    A hA hsampled hexpected

end SHS
