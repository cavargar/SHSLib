import SHSLib.Core.DavisHoldingSignedHistoryThresholdData

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # History-dependent capped reset occupation identity

The reset occupation density varies with the pre-jump state.  Its simple
approximations therefore use the history-localized threshold data introduced in
the preceding modules.  This file exposes the resulting signed conditional
identity directly at the capped reset-compensator endpoint.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- History-localized signed threshold approximations and integrability imply
the capped sampled reset-occupation identity on every pre-jump event. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.integral_cappedSampledResetOccupation_eq_expected_of_historyData
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (g : DavisState Q n → ℝ) (k : ℕ) (u : ℝ≥0)
    (hdata : DavisHoldingSignedHistoryThresholdApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
      (davisCappedSampledResetOccupationCompensator S hflow g ξ initial k u)
      (fun ω => davisSegmentExpectedResetCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState u))
    (A : Set Ω)
    (hA : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k] A)
    (hsampled : IntegrableOn
      (davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k u) A P)
    (hexpected : IntegrableOn (fun ω =>
      davisSegmentExpectedResetCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState u) A P) :
    ∫ ω in A, davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k u ω ∂P =
      ∫ ω in A, davisSegmentExpectedResetCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState u ∂P := by
  exact hlaw.integral_of_signedHistoryThresholdData k
    (davisCappedSampledResetOccupationCompensator S hflow g ξ initial k u)
    (fun ω => davisSegmentExpectedResetCompensator S hflow g
      (davisPreJumpHistory S hflow ξ initial k ω).currentState u)
    hdata A hA hsampled hexpected

end SHS
