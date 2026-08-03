import SHSLib.Core.DavisHoldingSignedThresholdData

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Conditional capped reset occupation identity

A deterministic cap is essential here: the conditional expectation of raw
occupation up to `min τ u` is the survivor-weighted expected reset compensator
up to `u`.  Without a cap, the right side would require an improper integral to
infinity, not evaluation at the random holding time.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Reset occupation on segment `k`, stopped at the smaller of its sampled
holding time and a deterministic duration cap. -/
def davisCappedSampledResetOccupationCompensator (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (k : ℕ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  davisSegmentResetOccupationCompensator S hflow g
    (davisPreJumpHistory S hflow ξ initial k ω).currentState
    (min (ξ.holdingTime k ω) u)

/-- Given matching signed threshold approximations and integrability, capped
sampled raw reset occupation has the finite survivor-weighted expected reset
compensator as its conditional integral on every pre-jump event. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.integral_cappedSampledResetOccupation_eq_expected
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (g : DavisState Q n → ℝ) (k : ℕ) (u : ℝ≥0)
    (hdata : DavisHoldingSignedThresholdApproximationData
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
  exact hlaw.integral_of_signedThresholdData k
    (davisCappedSampledResetOccupationCompensator S hflow g ξ initial k u)
    (fun ω => davisSegmentExpectedResetCompensator S hflow g
      (davisPreJumpHistory S hflow ξ initial k ω).currentState u) hdata A hA hsampled hexpected

end SHS
