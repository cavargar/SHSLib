import SHSLib.Core.DavisFiniteResetOccupationBridge

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Finite capped occupation-centered reset sums

This module isolates the finite algebraic assembly needed after the holding-time
and channel conditional laws have been established.  A reset is counted only
when its sampled holding time lies below the deterministic duration cap; it is
then centered by the raw reset occupation through the same capped duration.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Realized reset increment on segment `k`, retained only when the jump occurs
before the deterministic duration cap. -/
def davisCappedRealizedResetIncrement (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (k : ℕ) (u : ℝ≥0) (ω : Ω) : ℝ :=
  if ξ.holdingTime k ω ≤ u then
    davisRealizedResetIncrement S hflow ξ initial g k ω
  else 0

/-- Finite sum of duration-capped realized reset increments. -/
def davisFiniteCappedRealizedResetSum (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (cap : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    davisCappedRealizedResetIncrement S hflow ξ initial g k (cap k) ω

/-- Finite duration-capped realized resets centered by their occupied reset
intensity. -/
def davisFiniteCappedOccupationCenteredResetSum (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (cap : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  davisFiniteCappedRealizedResetSum S hflow ξ initial g cap N ω -
    davisFiniteCappedResetOccupation S hflow g ξ initial cap N ω

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- If the channel and holding-time laws identify the expectation of each
capped realized reset and each capped raw occupation with the same predictable
quantity, then the finite occupation-centered sum has expectation zero. -/
theorem integral_davisFiniteCappedOccupationCenteredResetSum_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (cap : ℕ → ℝ≥0) (N : ℕ)
    (hreal : ∀ k < N, Integrable
      (davisCappedRealizedResetIncrement S hflow ξ initial g k (cap k)) P)
    (hocc : ∀ k < N, Integrable
      (davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k (cap k)) P)
    (hmatch : ∀ k < N,
      ∫ ω, davisCappedRealizedResetIncrement
          S hflow ξ initial g k (cap k) ω ∂P =
        ∫ ω, davisCappedSampledResetOccupationCompensator
          S hflow g ξ initial k (cap k) ω ∂P) :
    ∫ ω, davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g cap N ω ∂P = 0 := by
  have hrealSum : Integrable
      (davisFiniteCappedRealizedResetSum S hflow ξ initial g cap N) P := by
    unfold davisFiniteCappedRealizedResetSum
    exact integrable_finset_sum (Finset.range N) fun k hk =>
      hreal k (Finset.mem_range.mp hk)
  have hoccSum : Integrable
      (davisFiniteCappedResetOccupation S hflow g ξ initial cap N) P := by
    unfold davisFiniteCappedResetOccupation
    exact integrable_finset_sum (Finset.range N) fun k hk =>
      hocc k (Finset.mem_range.mp hk)
  unfold davisFiniteCappedOccupationCenteredResetSum
  rw [integral_sub hrealSum hoccSum]
  change (∫ ω, ∑ k ∈ Finset.range N,
      davisCappedRealizedResetIncrement
        S hflow ξ initial g k (cap k) ω ∂P) -
    (∫ ω, ∑ k ∈ Finset.range N,
      davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k (cap k) ω ∂P) = 0
  rw [integral_finset_sum, integral_finset_sum]
  · rw [Finset.sum_congr rfl fun k hk =>
      hmatch k (Finset.mem_range.mp hk)]
    ring
  · intro k hk
    exact hocc k (Finset.mem_range.mp hk)
  · intro k hk
    exact hreal k (Finset.mem_range.mp hk)

end SHS
