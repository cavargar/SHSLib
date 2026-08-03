import SHSLib.Core.DavisFiniteResetOccupationBridge
import SHSLib.Core.DavisSegmentCompensator

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Reset occupation at fixed elapsed time

Completed segments contribute their full raw reset occupation, while the active
segment contributes only through its current elapsed duration.  The resulting
pathwise compensator is related explicitly to the earlier jump-index
compensator and yields an occupation-centered version of the telescoping
identity.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Raw reset occupation accumulated by elapsed time `t`. -/
def davisElapsedResetOccupation (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  let k := ξ.activeSegmentIndex hne t ω
  davisFiniteResetOccupation S hflow g ξ initial k ω +
    davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial k ω)
      (t - ξ.jumpTime k ω)

/-- Realized completed resets centered by raw reset occupation through `t`. -/
def davisElapsedOccupationCenteredResetSum (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisElapsedRealizedResetSum S hflow ξ hne initial g t ω -
    davisElapsedResetOccupation S hflow ξ hne initial g t ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The occupation-centered reset process is the established channel-centered
process plus the predictable-compensator discrepancy. -/
theorem davisElapsedOccupationCenteredResetSum_eq_channelCentered_add_gap
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    davisElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g t ω =
      davisElapsedCenteredResetSum S hflow ξ hne initial g t ω +
        (davisElapsedExpectedResetSum S hflow ξ hne initial g t ω -
          davisElapsedResetOccupation S hflow ξ hne initial g t ω) := by
  rw [davisElapsedCenteredResetSum_eq_realized_sub_expected]
  unfold davisElapsedOccupationCenteredResetSum
  ring

/-- Flow occupation plus raw reset occupation is the pathwise extended-generator
compensator assembled from the supplied flow density and reset test function. -/
def davisElapsedOccupationCompensator (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (a g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisElapsedFlowCompensator S hflow ξ hne initial a t ω +
    davisElapsedResetOccupation S hflow ξ hne initial g t ω

/-- The test-function increment compensated by occupied flow and reset
densities is exactly the occupation-centered realized-reset process. -/
theorem davis_compensatedProcess_eq_elapsedOccupationCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g a : DavisState Q n → ℝ)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (t : ℝ≥0) (ω : Ω) :
    g (davisJumpPath S hflow ξ hne initial t ω) - g initial -
        davisElapsedOccupationCompensator
          S hflow ξ hne initial a g t ω =
      davisElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g t ω := by
  have hchannel := davis_compensatedProcess_eq_elapsedCenteredResetSum
    S hflow ξ hne initial g a hga t ω
  have hgap := davisElapsedOccupationCenteredResetSum_eq_channelCentered_add_gap
    S hflow ξ hne initial g t ω
  unfold davisElapsedOccupationCompensator davisElapsedSegmentCompensator at *
  linarith

end SHS
