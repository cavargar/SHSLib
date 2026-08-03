import SHSLib.Core.DavisFiniteOccupationCentered

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Removing deterministic duration caps from finite occupation sums -/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Once every sampled holding time among the first `N` segments is below its
cap, the capped realized-reset sum is the full finite realized-reset sum. -/
theorem davisFiniteCappedRealizedResetSum_eq_full_of_holdingTime_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (cap : ℕ → ℝ≥0) (N : ℕ) (ω : Ω)
    (hcap : ∀ k < N, ξ.holdingTime k ω ≤ cap k) :
    davisFiniteCappedRealizedResetSum S hflow ξ initial g cap N ω =
      davisFiniteRealizedResetSum S hflow ξ initial g N ω := by
  apply Finset.sum_congr rfl
  intro k hk
  unfold davisCappedRealizedResetIncrement
  rw [if_pos (hcap k (Finset.mem_range.mp hk))]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Under the same cap condition, the capped occupation-centered sum is the
full finite occupation-centered sum. -/
theorem davisFiniteCappedOccupationCenteredResetSum_eq_full_of_holdingTime_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (cap : ℕ → ℝ≥0) (N : ℕ) (ω : Ω)
    (hcap : ∀ k < N, ξ.holdingTime k ω ≤ cap k) :
    davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g cap N ω =
      davisFiniteOccupationCenteredResetSum
        S hflow ξ initial g N ω := by
  unfold davisFiniteCappedOccupationCenteredResetSum
    davisFiniteOccupationCenteredResetSum
  rw [davisFiniteCappedRealizedResetSum_eq_full_of_holdingTime_le
      S hflow ξ initial g cap N ω hcap,
    davisFiniteCappedResetOccupation_eq_full_of_holdingTime_le
      S hflow g ξ initial cap N ω hcap]

end SHS
