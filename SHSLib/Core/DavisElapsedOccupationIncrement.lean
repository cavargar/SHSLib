import SHSLib.Core.DavisElapsedOccupationEventCentering

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Increments of the elapsed occupation-centered reset process

The fixed-time occupation-centered sums form a time-indexed process.  This
module records its increments and separates, pathwise, the completed-reset
increment from the reset-occupation increment.  The decomposition is purely
algebraic and does not require an ordering assumption on the two times.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The elapsed occupation-centered reset sum viewed as a time-indexed process. -/
def davisElapsedOccupationCenteredResetProcess (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t => davisElapsedOccupationCenteredResetSum
    S hflow ξ hne initial g t

/-- Increment of the elapsed occupation-centered reset process from `s` to `t`. -/
def davisElapsedOccupationCenteredResetIncrement (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (s t : ℝ≥0) (ω : Ω) : ℝ :=
  davisElapsedOccupationCenteredResetProcess
      S hflow ξ hne initial g t ω -
    davisElapsedOccupationCenteredResetProcess
      S hflow ξ hne initial g s ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A centered increment is the realized-reset increment minus the increment
of raw reset occupation. -/
theorem davisElapsedOccupationCenteredResetIncrement_eq_realized_sub_occupation
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (s t : ℝ≥0) (ω : Ω) :
    davisElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g s t ω =
      (davisElapsedRealizedResetSum S hflow ξ hne initial g t ω -
        davisElapsedRealizedResetSum S hflow ξ hne initial g s ω) -
      (davisElapsedResetOccupation S hflow ξ hne initial g t ω -
        davisElapsedResetOccupation S hflow ξ hne initial g s ω) := by
  unfold davisElapsedOccupationCenteredResetIncrement
  simp only [davisElapsedOccupationCenteredResetProcess]
  unfold davisElapsedOccupationCenteredResetSum
  ring

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Additivity of elapsed occupation-centered increments at an intermediate
fixed time. -/
theorem davisElapsedOccupationCenteredResetIncrement_add
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (r s t : ℝ≥0) (ω : Ω) :
    davisElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g r s ω +
      davisElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g s t ω =
      davisElapsedOccupationCenteredResetIncrement
        S hflow ξ hne initial g r t ω := by
  rw [davisElapsedOccupationCenteredResetIncrement_eq_realized_sub_occupation,
      davisElapsedOccupationCenteredResetIncrement_eq_realized_sub_occupation,
      davisElapsedOccupationCenteredResetIncrement_eq_realized_sub_occupation]
  ring

end SHS
