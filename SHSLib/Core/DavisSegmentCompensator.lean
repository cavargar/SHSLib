import SHSLib.Core.DavisResetDecomposition

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Segmentwise flow and reset compensators

This module converts the pathwise flow increments in the Davis jump recursion
into integrals of a supplied flow density.  The only analytic assumption is the
fundamental-theorem identity along every deterministic flow segment.  Combining
this identity with the reset decomposition gives a centered-process formula at
an arbitrary elapsed time.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Integral of a real-valued density along one deterministic Davis flow
segment of elapsed length `u`. -/
def davisFlowDensityIntegral (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (a : DavisState Q n → ℝ) (z : DavisState Q n) (u : ℝ≥0) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
    a (davisFlow S hflow s.toNNReal z)

/-- Fundamental-theorem identity required of a test function and its flow
density.  For generator applications, `g` is the lifted test function and `a`
is its deterministic-flow generator. -/
def DavisFlowIntegralIdentity (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g a : DavisState Q n → ℝ) : Prop :=
  ∀ z u, g (davisFlow S hflow u z) - g z =
    davisFlowDensityIntegral S hflow a z u

/-- Sum of density integrals over the first `N` completed deterministic
segments. -/
def davisFiniteFlowCompensator (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (a : DavisState Q n → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    davisFlowDensityIntegral S hflow a
      (davisStateAfterJump S hflow ξ initial k ω) (ξ.holdingTime k ω)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The completed deterministic-flow increments equal their segmentwise
density integrals. -/
theorem davisFiniteFlowIncrementSum_eq_compensator
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g a : DavisState Q n → ℝ)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (N : ℕ) (ω : Ω) :
    davisFiniteFlowIncrementSum S hflow ξ initial g N ω =
      davisFiniteFlowCompensator S hflow ξ initial a N ω := by
  apply Finset.sum_congr rfl
  intro k hk
  exact hga (davisStateAfterJump S hflow ξ initial k ω)
    (ξ.holdingTime k ω)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The assembled path is the unclamped flow from the active post-jump state
for exactly the elapsed time since the active segment began. -/
theorem davisJumpPath_eq_activeFlow
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (t : ℝ≥0) (ω : Ω) :
    davisJumpPath S hflow ξ hne initial t ω =
      davisFlow S hflow
        (t - ξ.jumpTime (ξ.activeSegmentIndex hne t ω) ω)
        (davisStateAfterJump S hflow ξ initial
          (ξ.activeSegmentIndex hne t ω) ω) := by
  simp only [davisJumpPath, davisJumpSegment]
  rw [min_eq_left]
  exact ξ.activeSegmentElapsed_le_holdingTime hne t ω

/-- Segmentwise flow compensator up to elapsed time `t`: completed segment
integrals plus the integral over the unfinished active segment. -/
def davisElapsedFlowCompensator (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (a : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  let k := ξ.activeSegmentIndex hne t ω
  davisFiniteFlowCompensator S hflow ξ initial a k ω +
    davisFlowDensityIntegral S hflow a
      (davisStateAfterJump S hflow ξ initial k ω)
      (t - ξ.jumpTime k ω)

/-- Total segmentwise compensator: deterministic-flow density integrals plus
normalized expected reset increments at completed jumps. -/
def davisElapsedSegmentCompensator (S : SHS Q n m)
    (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (a : DavisState Q n → ℝ)
    (g : DavisState Q n → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  davisElapsedFlowCompensator S hflow ξ hne initial a t ω +
    davisElapsedExpectedResetSum S hflow ξ hne initial g t ω

/-- The compensated test-function process is exactly the elapsed centered reset
sum.  This is a pathwise identity; probabilistic martingale consequences can
therefore be transferred from the centered reset sum. -/
theorem davis_compensatedProcess_eq_elapsedCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g a : DavisState Q n → ℝ)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (t : ℝ≥0) (ω : Ω) :
    g (davisJumpPath S hflow ξ hne initial t ω) - g initial -
        davisElapsedSegmentCompensator S hflow ξ hne initial a g t ω =
      davisElapsedCenteredResetSum S hflow ξ hne initial g t ω := by
  let k := ξ.activeSegmentIndex hne t ω
  have hflowCompleted := davisFiniteFlowIncrementSum_eq_compensator
    S hflow ξ initial g a hga k ω
  have hflowActive := hga
    (davisStateAfterJump S hflow ξ initial k ω)
    (t - ξ.jumpTime k ω)
  have hpath := davisJumpPath_telescope
    S hflow ξ hne initial g t ω
  have hactivePath := davisJumpPath_eq_activeFlow
    S hflow ξ hne initial t ω
  have hreset := davisElapsedCenteredResetSum_eq_realized_sub_expected
    S hflow ξ hne initial g t ω
  simp only [davisElapsedSegmentCompensator, davisElapsedFlowCompensator]
  simp only [k] at hflowCompleted hflowActive hpath hactivePath hreset ⊢
  rw [hactivePath] at hpath ⊢
  linarith

/-- At every fixed elapsed time, the segmentwise compensated process has mean
zero whenever the completed-jump count is integrable. -/
theorem DavisJumpNoise.ConditionalChannelLaw.integral_compensatedProcess_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {initial : DavisState Q n}
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (hlaw : ξ.ConditionalChannelLaw S hflow P initial)
    (g a : DavisState Q n → ℝ) (hgmeas : Measurable g)
    (C : ℝ) (hg : ∀ z, |g z| ≤ C)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (t : ℝ≥0)
    (hcount : Integrable (fun ω => (ξ.activeSegmentIndex hne t ω : ℝ)) P) :
    ∫ ω, (g (davisJumpPath S hflow ξ hne initial t ω) - g initial -
      davisElapsedSegmentCompensator S hflow ξ hne initial a g t ω) ∂P = 0 := by
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun ω =>
      davis_compensatedProcess_eq_elapsedCenteredResetSum
        S hflow ξ hne initial g a hga t ω)]
  exact hlaw.integral_elapsedCenteredResetSum_eq_zero
    hf hr hξ hne g hgmeas C hg t hcount

end SHS
