import SHSLib.Core.DavisFiniteCompensatorMeasurable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Uniform bounds for finite centered reset sums

The estimates here provide the domination needed to upgrade measurable finite
reset sums to integrable random variables on a probability space.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The normalized expected reset increment satisfies the bounded-function
estimate even at states where the total intensity vanishes. -/
theorem abs_davisExpectedResetIncrement_le_all
    (S : SHS Q n m) (g : DavisState Q n → ℝ) (z : DavisState Q n)
    (C : ℝ) (hg : ∀ y, |g y| ≤ C) :
    |davisExpectedResetIncrement S g z| ≤ 2 * C := by
  by_cases hz : S.totalIntensity z = 0
  · unfold davisExpectedResetIncrement davisChannelProbability
    simp [hz]
    linarith [abs_nonneg (g z), hg z]
  · exact abs_davisExpectedResetIncrement_le S g z C hg hz

/-- An actual reset changes a `C`-bounded test function by at most `2 C`. -/
theorem abs_davisRealizedResetIncrement_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (k : ℕ) (ω : Ω) :
    |davisRealizedResetIncrement S hflow ξ initial g k ω| ≤ 2 * C := by
  unfold davisRealizedResetIncrement
  calc |g (S.resetDavisState (ξ.channel k ω) (davisStateBeforeJump S hflow ξ initial k ω)) -
        g (davisStateBeforeJump S hflow ξ initial k ω)|
      ≤ |g (S.resetDavisState (ξ.channel k ω) (davisStateBeforeJump S hflow ξ initial k ω))| +
        |g (davisStateBeforeJump S hflow ξ initial k ω)| := abs_sub _ _
    _ ≤ C + C := by linarith [hg (S.resetDavisState (ξ.channel k ω) (davisStateBeforeJump S hflow ξ initial k ω)),
                              hg (davisStateBeforeJump S hflow ξ initial k ω)]
    _ = 2 * C := by ring

/-- A centered one-step reset increment of a `C`-bounded function has absolute
value at most `4 C`. -/
theorem abs_davisCenteredResetIncrement_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (k : ℕ) (ω : Ω) :
    |davisCenteredResetIncrement S hflow ξ initial g k ω| ≤ 4 * C := by
  unfold davisCenteredResetIncrement
  calc |davisRealizedResetIncrement S hflow ξ initial g k ω -
        davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω)|
      ≤ |davisRealizedResetIncrement S hflow ξ initial g k ω| +
        |davisExpectedResetIncrement S g (davisStateBeforeJump S hflow ξ initial k ω)| := abs_sub _ _
    _ ≤ 2 * C + 2 * C := by
        apply add_le_add
        · exact abs_davisRealizedResetIncrement_le S hflow ξ initial g C hg k ω
        · exact abs_davisExpectedResetIncrement_le_all S g _ C hg
    _ = 4 * C := by ring

/-- The finite sum through `N` jumps is bounded linearly in `N`. -/
theorem abs_davisFiniteCenteredResetSum_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (N : ℕ) (ω : Ω) :
    |davisFiniteCenteredResetSum S hflow ξ initial g N ω| ≤
      (N : ℝ) * (4 * C) := by
  unfold davisFiniteCenteredResetSum
  calc |∑ k ∈ Finset.range N, davisCenteredResetIncrement S hflow ξ initial g k ω|
      ≤ ∑ k ∈ Finset.range N, |davisCenteredResetIncrement S hflow ξ initial g k ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, 4 * C := by
        apply Finset.sum_le_sum
        intro k _
        exact abs_davisCenteredResetIncrement_le S hflow ξ initial g C hg k ω
    _ = (N : ℝ) * (4 * C) := by simp

/-- On a finite measure space, measurable finite centered reset sums of a
bounded test function are integrable. -/
theorem DavisJumpNoise.MeasurableNoise.integrable_finiteCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hgmeas : Measurable g) (C : ℝ) (hg : ∀ y, |g y| ≤ C) (N : ℕ) :
    Integrable (davisFiniteCenteredResetSum S hflow ξ initial g N) P := by
  refine Integrable.mono' (integrable_const ((N : ℝ) * (4 * C)))
    (hξ.finiteCenteredResetSum S hflow hf hr initial g hgmeas N).aestronglyMeasurable ?_
  filter_upwards with ω
  simpa only [Real.norm_eq_abs] using
    abs_davisFiniteCenteredResetSum_le S hflow ξ initial g C hg N ω

end SHS
