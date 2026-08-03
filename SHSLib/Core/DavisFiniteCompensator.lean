import SHSLib.Core.DavisOneStepLaw

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Finite reset-compensator sums

This module introduces the realized and conditionally centered reset increments
along the pathwise Davis jump recursion.  It records their finite-sum algebra
and bounded-test-function estimates, preparing the discrete martingale and
continuous-time compensator constructions.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Increment of `g` produced by the reset at jump index `k`. -/
def davisRealizedResetIncrement (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  g (S.resetDavisState (ξ.channel k ω)
      (davisStateBeforeJump S hflow ξ initial k ω)) -
    g (davisStateBeforeJump S hflow ξ initial k ω)

/-- The realized reset increment is the difference between the post-reset and
pre-reset values of the test function. -/
theorem davisRealizedResetIncrement_eq_state_difference
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (k : ℕ) (ω : Ω) :
    davisRealizedResetIncrement S hflow ξ initial g k ω =
      g (davisStateAfterJump S hflow ξ initial (k + 1) ω) -
        g (davisStateBeforeJump S hflow ξ initial k ω) := by
  rfl

/-- Reset increment centered by its normalized channel expectation at the
pre-reset state. -/
def davisCenteredResetIncrement (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  davisRealizedResetIncrement S hflow ξ initial g k ω -
    davisExpectedResetIncrement S g
      (davisStateBeforeJump S hflow ξ initial k ω)

/-- Finite sum of centered reset increments before jump index `N`. -/
def davisFiniteCenteredResetSum (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    davisCenteredResetIncrement S hflow ξ initial g k ω

@[simp] theorem davisFiniteCenteredResetSum_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (ω : Ω) :
    davisFiniteCenteredResetSum S hflow ξ initial g 0 ω = 0 := by
  rfl

/-- Adding one jump adds exactly its centered one-step increment. -/
theorem davisFiniteCenteredResetSum_succ
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) :
    davisFiniteCenteredResetSum S hflow ξ initial g (N + 1) ω =
      davisFiniteCenteredResetSum S hflow ξ initial g N ω +
        davisCenteredResetIncrement S hflow ξ initial g N ω := by
  simp [davisFiniteCenteredResetSum, Finset.sum_range_succ]

/-- At nonzero total intensity, the normalized expected reset increment is the
expected post-reset value minus the current value. -/
theorem davisExpectedResetIncrement_eq_expected_value_sub
    (S : SHS Q n m) (g : DavisState Q n → ℝ) (z : DavisState Q n)
    (hz : S.totalIntensity z ≠ 0) :
    davisExpectedResetIncrement S g z =
      (∑ ℓ : Fin m, davisChannelProbability S z ℓ *
        g (S.resetDavisState ℓ z)) - g z := by
  unfold davisExpectedResetIncrement
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  rw [sum_davisChannelProbability S z hz]
  simp

/-- A bounded test function has normalized expected reset increment bounded by
`2 * C`. -/
theorem abs_davisExpectedResetIncrement_le
    (S : SHS Q n m) (g : DavisState Q n → ℝ) (z : DavisState Q n)
    (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (hz : S.totalIntensity z ≠ 0) :
    |davisExpectedResetIncrement S g z| ≤ 2 * C := by
  unfold davisExpectedResetIncrement
  calc |∑ ℓ : Fin m, davisChannelProbability S z ℓ * (g (S.resetDavisState ℓ z) - g z)|
      ≤ ∑ ℓ : Fin m, |davisChannelProbability S z ℓ * (g (S.resetDavisState ℓ z) - g z)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ℓ : Fin m, davisChannelProbability S z ℓ * |g (S.resetDavisState ℓ z) - g z| := by
        congr 1; ext ℓ; rw [abs_mul, abs_of_nonneg (davisChannelProbability_nonneg S z ℓ)]
    _ ≤ ∑ ℓ : Fin m, davisChannelProbability S z ℓ * (2 * C) := by
        apply Finset.sum_le_sum
        intro ℓ _
        apply mul_le_mul_of_nonneg_left _ (davisChannelProbability_nonneg S z ℓ)
        calc |g (S.resetDavisState ℓ z) - g z| ≤ |g (S.resetDavisState ℓ z)| + |g z| := abs_sub _ _
          _ ≤ C + C := by linarith [hg (S.resetDavisState ℓ z), hg z]
          _ = 2 * C := by ring
    _ = 2 * C * ∑ ℓ : Fin m, davisChannelProbability S z ℓ := by
        rw [mul_comm, Finset.mul_sum]
        congr 1; ext ℓ; ring
    _ = 2 * C * 1 := by rw [sum_davisChannelProbability S z hz]
    _ = 2 * C := by ring

/-- The absolute reset-compensator density of a bounded test function is at
most `2 * C` times the total jump intensity. -/
theorem abs_resetCompensator_le_two_mul_totalIntensity
    (S : SHS Q n m) (g : DavisState Q n → ℝ) (z : DavisState Q n)
    (C : ℝ) (hg : ∀ y, |g y| ≤ C) :
    |∑ ℓ : Fin m, (g (S.resetDavisState ℓ z) - g z) *
        S.intensity ℓ z.1 z.2.1 z.2.2| ≤
      2 * C * S.totalIntensity z := by
  rw [← totalIntensity_mul_davisExpectedResetIncrement]
  by_cases hz : S.totalIntensity z = 0
  · simp [hz]
  · have h := abs_davisExpectedResetIncrement_le S g z C hg hz
    rw [abs_mul, abs_of_nonneg (totalIntensity_nonneg S z)]
    linarith [mul_le_mul_of_nonneg_right h (totalIntensity_nonneg S z)]

end SHS
