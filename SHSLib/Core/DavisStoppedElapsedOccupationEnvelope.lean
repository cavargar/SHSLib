import SHSLib.Core.DavisStoppedElapsedOccupationMeasurable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # A common envelope for jump-capped elapsed occupation

The stopped elapsed occupation-centered sums are uniformly dominated by the
absolute realized increments and reset occupations through the active segment.
This pathwise envelope is independent of the deterministic jump cap.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Cap-independent fixed-time envelope: absolute completed realized reset
increments, absolute completed reset occupations, and the active partial reset
occupation. -/
def davisElapsedOccupationEnvelope (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  let k := ξ.activeSegmentIndex hne t ω
  (∑ i ∈ Finset.range k,
      |davisRealizedResetIncrement S hflow ξ initial g i ω|) +
    (∑ i ∈ Finset.range k,
      |davisSampledResetOccupationCompensator S hflow g ξ initial i ω|) +
    |davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial k ω)
      (t - ξ.jumpTime k ω)|

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Every deterministic jump-capped elapsed occupation-centered sum is bounded
by the same full fixed-time envelope. -/
theorem abs_davisStoppedElapsedOccupationCenteredResetSum_le_envelope
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    |davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t ω| ≤
      davisElapsedOccupationEnvelope S hflow ξ hne initial g t ω := by
  unfold davisStoppedElapsedOccupationCenteredResetSum
  unfold davisElapsedOccupationEnvelope
  unfold davisFiniteRealizedResetSum
  unfold davisStoppedElapsedResetOccupation
  unfold davisFiniteResetOccupation
  set k := ξ.activeSegmentIndex hne t ω with hk
  let realized := ∑ i ∈ Finset.range (min N k), S.davisRealizedResetIncrement hflow ξ initial g i ω
  let occupation := ∑ i ∈ Finset.range (min N k), S.davisSegmentResetOccupationCompensator hflow g (S.davisPreJumpHistory hflow ξ initial i ω).currentState (ξ.holdingTime i ω)
  let segment := S.davisSegmentResetOccupationCompensator hflow g (S.davisStateAfterJump hflow ξ initial k ω) (t - ξ.jumpTime k ω)
  have h1 : |realized - (occupation + if k < N then segment else 0)| ≤ |realized| + |occupation + if k < N then segment else 0| := by
    have hab := abs_add_le realized (-(occupation + if k < N then segment else 0))
    simp only [← sub_eq_add_neg] at hab
    linarith [hab, abs_neg (occupation + if k < N then segment else 0)]
  have h2 : |realized| ≤ ∑ i ∈ Finset.range (min N k), |S.davisRealizedResetIncrement hflow ξ initial g i ω| := by
    apply Finset.abs_sum_le_sum_abs
  have h3 : |occupation + if k < N then segment else 0| ≤ |occupation| + |if k < N then segment else 0| := by
    have hab := abs_add_le occupation (if k < N then segment else 0)
    exact hab
  have h4 : |occupation| ≤ ∑ i ∈ Finset.range (min N k), |davisSampledResetOccupationCompensator S hflow g ξ initial i ω| := by
    simp only [davisSampledResetOccupationCompensator]
    apply Finset.abs_sum_le_sum_abs
  have h5 : |if k < N then segment else 0| ≤ |segment| := by
    split_ifs <;> simp
  have h6 : ∑ i ∈ Finset.range (min N k), |S.davisRealizedResetIncrement hflow ξ initial g i ω| ≤ ∑ i ∈ Finset.range k, |S.davisRealizedResetIncrement hflow ξ initial g i ω| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right _ _))
    intro _ _ _; exact abs_nonneg _
  have h7 : ∑ i ∈ Finset.range (min N k), |davisSampledResetOccupationCompensator S hflow g ξ initial i ω| ≤ ∑ i ∈ Finset.range k, |davisSampledResetOccupationCompensator S hflow g ξ initial i ω| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_right _ _))
    intro _ _ _; exact abs_nonneg _
  have h8 : |realized| + |occupation + if k < N then segment else 0| ≤
      ∑ i ∈ Finset.range (min N k), |S.davisRealizedResetIncrement hflow ξ initial g i ω| +
      (∑ i ∈ Finset.range (min N k), |davisSampledResetOccupationCompensator S hflow g ξ initial i ω| + |if k < N then segment else 0|) := by
    linarith [h1, h2, h3, h4, h5]
  linarith [h8, h6, h7]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Integrability of the common envelope immediately gives integrability of
every measurable stopped elapsed approximation. -/
theorem integrable_davisStoppedElapsedOccupationCenteredResetSum_of_envelope
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (t : ℝ≥0)
    (hmeas : AEStronglyMeasurable
      (davisStoppedElapsedOccupationCenteredResetSum
        S hflow ξ hne initial g N t) P)
    (henvelope : Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Integrable (davisStoppedElapsedOccupationCenteredResetSum
      S hflow ξ hne initial g N t) P := by
  apply Integrable.mono' henvelope hmeas
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_davisStoppedElapsedOccupationCenteredResetSum_le_envelope
    S hflow ξ hne initial g N t ω

end SHS
