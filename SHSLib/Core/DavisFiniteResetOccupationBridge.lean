import SHSLib.Core.DavisFiniteResetOccupation
import SHSLib.Core.DavisResetDecomposition

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Full finite reset occupations and centered decompositions

A deterministic cap disappears once it exceeds the sampled holding time.  This
provides the pathwise bridge from the capped conditional identities to full
completed segments and records how the resulting occupation-centered reset sum
compares with the established channel-centered reset martingale.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Raw reset occupation over the first `N` complete sampled segments. -/
def davisFiniteResetOccupation (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    davisSegmentResetOccupationCompensator S hflow g
      (davisPreJumpHistory S hflow ξ initial k ω).currentState
      (ξ.holdingTime k ω)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- If every sampled duration among the first `N` segments lies below its cap,
the capped finite occupation is already the full finite occupation. -/
theorem davisFiniteCappedResetOccupation_eq_full_of_holdingTime_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (cap : ℕ → ℝ≥0) (N : ℕ) (ω : Ω)
    (hcap : ∀ k < N, ξ.holdingTime k ω ≤ cap k) :
    davisFiniteCappedResetOccupation S hflow g ξ initial cap N ω =
      davisFiniteResetOccupation S hflow g ξ initial N ω := by
  apply Finset.sum_congr rfl
  intro k hk
  unfold davisCappedSampledResetOccupationCompensator
  rw [min_eq_left (hcap k (Finset.mem_range.mp hk))]

/-- Realized reset increments centered by full raw occupation along completed
segments. -/
def davisFiniteOccupationCenteredResetSum (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  davisFiniteRealizedResetSum S hflow ξ initial g N ω -
    davisFiniteResetOccupation S hflow g ξ initial N ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Occupation-centering differs from channel-centering by exactly the gap
between the jump-index predictable sum and the raw occupied-time integral. -/
theorem davisFiniteOccupationCenteredResetSum_eq_channelCentered_add_gap
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) :
    davisFiniteOccupationCenteredResetSum S hflow ξ initial g N ω =
      davisFiniteCenteredResetSum S hflow ξ initial g N ω +
        (davisFiniteExpectedResetSum S hflow ξ initial g N ω -
          davisFiniteResetOccupation S hflow g ξ initial N ω) := by
  rw [davisFiniteCenteredResetSum_eq_realized_sub_expected]
  unfold davisFiniteOccupationCenteredResetSum
  ring

end SHS
