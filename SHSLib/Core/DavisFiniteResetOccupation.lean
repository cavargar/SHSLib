import SHSLib.Core.DavisResetOccupationRectangular

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Finite sums of capped reset occupations

The one-segment conditional occupation identity is stable under deterministic
finite summation.  This file packages the sampled and survivor-weighted sides
and supplies both an algebraic summation theorem and a specialization using the
rectangular approximation interface.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Sum of capped sampled reset occupations over the first `N` segments. -/
def davisFiniteCappedResetOccupation (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (cap : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    davisCappedSampledResetOccupationCompensator
      S hflow g ξ initial k (cap k) ω

/-- Sum of the survivor-weighted deterministic compensators corresponding to
those same segment caps. -/
def davisFiniteExpectedResetOccupation (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (cap : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    davisSegmentExpectedResetCompensator S hflow g
      (davisPreJumpHistory S hflow ξ initial k ω).currentState (cap k)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Finite summation of one-segment integral identities. -/
theorem integral_davisFiniteCappedResetOccupation_eq_expected
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (g : DavisState Q n → ℝ) (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (cap : ℕ → ℝ≥0) (N : ℕ)
    (hsampled : ∀ k < N, Integrable
      (davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k (cap k)) P)
    (hexpected : ∀ k < N, Integrable (fun ω =>
      davisSegmentExpectedResetCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState (cap k)) P)
    (hone : ∀ k < N,
      ∫ ω, davisCappedSampledResetOccupationCompensator
          S hflow g ξ initial k (cap k) ω ∂P =
        ∫ ω, davisSegmentExpectedResetCompensator S hflow g
          (davisPreJumpHistory S hflow ξ initial k ω).currentState (cap k) ∂P) :
    ∫ ω, davisFiniteCappedResetOccupation
        S hflow g ξ initial cap N ω ∂P =
      ∫ ω, davisFiniteExpectedResetOccupation
        S hflow g ξ initial cap N ω ∂P := by
  change (∫ ω, ∑ k ∈ Finset.range N,
      davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k (cap k) ω ∂P) =
    ∫ ω, ∑ k ∈ Finset.range N,
      davisSegmentExpectedResetCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState (cap k) ∂P
  rw [MeasureTheory.integral_finset_sum, MeasureTheory.integral_finset_sum]
  · exact Finset.sum_congr rfl (fun k hk => hone k (Finset.mem_range.mp hk))
  · intro k hk
    exact hexpected k (Finset.mem_range.mp hk)
  · intro k hk
    exact hsampled k (Finset.mem_range.mp hk)

/-- Rectangular positive/negative approximation data for every segment imply
the finite capped occupation identity. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.integral_finiteCappedResetOccupation_eq_expected_of_rectangles
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (g : DavisState Q n → ℝ) (cap : ℕ → ℝ≥0) (N : ℕ)
    (hpos : ∀ k < N, DavisHoldingHistoryRectangularApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
      (fun ω => ENNReal.ofReal
        (davisCappedSampledResetOccupationCompensator
          S hflow g ξ initial k (cap k) ω))
      (fun ω => ENNReal.ofReal
        (davisSegmentExpectedResetCompensator S hflow g
          (davisPreJumpHistory S hflow ξ initial k ω).currentState (cap k))))
    (hneg : ∀ k < N, DavisHoldingHistoryRectangularApproximationData
      (S := S) (hflow := hflow) (hf := hf) (hr := hr) hξ initial k
      (fun ω => ENNReal.ofReal
        (-davisCappedSampledResetOccupationCompensator
          S hflow g ξ initial k (cap k) ω))
      (fun ω => ENNReal.ofReal
        (-davisSegmentExpectedResetCompensator S hflow g
          (davisPreJumpHistory S hflow ξ initial k ω).currentState (cap k))))
    (hsampled : ∀ k < N, Integrable
      (davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k (cap k)) P)
    (hexpected : ∀ k < N, Integrable (fun ω =>
      davisSegmentExpectedResetCompensator S hflow g
        (davisPreJumpHistory S hflow ξ initial k ω).currentState (cap k)) P) :
    ∫ ω, davisFiniteCappedResetOccupation
        S hflow g ξ initial cap N ω ∂P =
      ∫ ω, davisFiniteExpectedResetOccupation
        S hflow g ξ initial cap N ω ∂P := by
  apply integral_davisFiniteCappedResetOccupation_eq_expected
    P g ξ initial cap N hsampled hexpected
  intro k hk
  simpa only [Measure.restrict_univ] using
    hlaw.integral_cappedSampledResetOccupation_eq_expected_of_rectangles
      g k (cap k) (hpos k hk) (hneg k hk) Set.univ (by measurability)
      (hsampled k hk).integrableOn (hexpected k hk).integrableOn

end SHS
