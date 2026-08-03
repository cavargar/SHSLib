import SHSLib.Core.DavisElapsedResetSum

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Pathwise reset and flow decomposition

This module separates the accumulated reset contribution into its realized,
predictable, and centered parts, and proves the pathwise telescoping identity
for the Davis jump recursion at a fixed elapsed time.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Sum of the realized reset increments before jump index `N`. -/
def davisFiniteRealizedResetSum (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N, davisRealizedResetIncrement S hflow ξ initial g k ω

/-- Sum of normalized expected reset increments before jump index `N`. -/
def davisFiniteExpectedResetSum (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    davisExpectedResetIncrement S g
      (davisStateBeforeJump S hflow ξ initial k ω)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- A finite centered reset sum is the realized sum minus its predictable
finite-jump compensator. -/
theorem davisFiniteCenteredResetSum_eq_realized_sub_expected
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) :
    davisFiniteCenteredResetSum S hflow ξ initial g N ω =
      davisFiniteRealizedResetSum S hflow ξ initial g N ω -
        davisFiniteExpectedResetSum S hflow ξ initial g N ω := by
  simp [davisFiniteCenteredResetSum, davisFiniteRealizedResetSum,
    davisFiniteExpectedResetSum, davisCenteredResetIncrement,
    Finset.sum_sub_distrib]

/-- Sum of changes of `g` along the completed deterministic flow segments. -/
def davisFiniteFlowIncrementSum (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    (g (davisStateBeforeJump S hflow ξ initial k ω) -
      g (davisStateAfterJump S hflow ξ initial k ω))

/-- The post-jump value after `N` jumps telescopes into the initial value, all
completed flow increments, and all completed realized reset increments. -/
theorem davisStateAfterJump_telescope
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) :
    g (davisStateAfterJump S hflow ξ initial N ω) - g initial =
      davisFiniteFlowIncrementSum S hflow ξ initial g N ω +
        davisFiniteRealizedResetSum S hflow ξ initial g N ω := by
  unfold davisFiniteFlowIncrementSum davisFiniteRealizedResetSum
  rw [← Finset.sum_add_distrib]
  -- Combine the two sums into one
  have h_eq : ∀ k ∈ Finset.range N,
      (g (davisStateBeforeJump S hflow ξ initial k ω) - g (davisStateAfterJump S hflow ξ initial k ω)) +
      davisRealizedResetIncrement S hflow ξ initial g k ω =
      g (davisStateAfterJump S hflow ξ initial (k + 1) ω) - g (davisStateAfterJump S hflow ξ initial k ω) := by
    intro k _
    rw [davisRealizedResetIncrement_eq_state_difference]
    ring
  rw [Finset.sum_congr rfl h_eq]
  -- Telescope the sum
  have h_telescope : ∀ M, g (davisStateAfterJump S hflow ξ initial M ω) - g initial =
      ∑ k ∈ Finset.range M, (g (davisStateAfterJump S hflow ξ initial (k + 1) ω) -
          g (davisStateAfterJump S hflow ξ initial k ω)) := by
    intro M
    induction M with
    | zero => simp [davisStateAfterJump_zero]
    | succ M ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring
  exact h_telescope N

/-- Realized reset increments completed by elapsed time `t`. -/
def davisElapsedRealizedResetSum (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisFiniteRealizedResetSum S hflow ξ initial g
    (ξ.activeSegmentIndex hne t ω) ω

/-- Predictable reset increments completed by elapsed time `t`. -/
def davisElapsedExpectedResetSum (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisFiniteExpectedResetSum S hflow ξ initial g
    (ξ.activeSegmentIndex hne t ω) ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The elapsed centered reset sum is the elapsed realized reset sum minus its
jump-index predictable compensator. -/
theorem davisElapsedCenteredResetSum_eq_realized_sub_expected
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    davisElapsedCenteredResetSum S hflow ξ hne initial g t ω =
      davisElapsedRealizedResetSum S hflow ξ hne initial g t ω -
        davisElapsedExpectedResetSum S hflow ξ hne initial g t ω := by
  exact davisFiniteCenteredResetSum_eq_realized_sub_expected
    S hflow ξ initial g (ξ.activeSegmentIndex hne t ω) ω

/-- At a fixed elapsed time, the test-function increment is the sum of all
completed flow increments, all completed reset increments, and the unfinished
flow increment in the active segment. -/
theorem davisJumpPath_telescope
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) :
    g (davisJumpPath S hflow ξ hne initial t ω) - g initial =
      davisFiniteFlowIncrementSum S hflow ξ initial g
          (ξ.activeSegmentIndex hne t ω) ω +
        davisElapsedRealizedResetSum S hflow ξ hne initial g t ω +
        (g (davisJumpPath S hflow ξ hne initial t ω) -
          g (davisStateAfterJump S hflow ξ initial
            (ξ.activeSegmentIndex hne t ω) ω)) := by
  have h := davisStateAfterJump_telescope S hflow ξ initial g
    (ξ.activeSegmentIndex hne t ω) ω
  unfold davisElapsedRealizedResetSum
  linarith

end SHS
