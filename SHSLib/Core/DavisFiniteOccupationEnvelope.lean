import SHSLib.Core.DavisFiniteOccupationCapRemoval
import SHSLib.Core.DavisFiniteCompensatorBounds
import SHSLib.Core.DavisResetOccupationIntegrable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Integrable envelopes for finite capped occupation sums

This module supplies cap-independent estimates for the realized part and a
finite-sum interface for combining it with integrable occupation envelopes.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Duration-capping cannot increase the uniform `2 C` bound on a realized
reset increment. -/
theorem abs_davisCappedRealizedResetIncrement_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (k : ℕ) (u : ℝ≥0) (ω : Ω) :
    |davisCappedRealizedResetIncrement S hflow ξ initial g k u ω| ≤ 2 * C := by
  unfold davisCappedRealizedResetIncrement
  split_ifs
  · unfold davisRealizedResetIncrement
    calc
      |g (S.resetDavisState (ξ.channel k ω)
          (davisStateBeforeJump S hflow ξ initial k ω)) -
          g (davisStateBeforeJump S hflow ξ initial k ω)|
          ≤ |g (S.resetDavisState (ξ.channel k ω)
              (davisStateBeforeJump S hflow ξ initial k ω))| +
            |g (davisStateBeforeJump S hflow ξ initial k ω)| := abs_sub _ _
      _ ≤ C + C := by
        linarith [hg (S.resetDavisState (ξ.channel k ω)
          (davisStateBeforeJump S hflow ξ initial k ω)),
          hg (davisStateBeforeJump S hflow ξ initial k ω)]
      _ = 2 * C := by ring
  · have hC : 0 ≤ C := le_trans (abs_nonneg _) (hg initial)
    simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC

/-- On a finite measure space, every capped realized reset increment of a
bounded measurable test function is integrable. -/
theorem DavisJumpNoise.MeasurableNoise.integrable_cappedRealizedResetIncrement
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hgmeas : Measurable g) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (k : ℕ) (u : ℝ≥0) :
    Integrable (davisCappedRealizedResetIncrement
      S hflow ξ initial g k u) P := by
  apply MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (|2 * C|)) _ ?_
  · have h_real_meas : Measurable (fun ω =>
        davisRealizedResetIncrement S hflow ξ initial g k ω) :=
      hξ.realizedResetIncrement S hflow hf hr initial g hgmeas k
    have h_holding_meas : Measurable (fun ω => (ξ.holdingTime k ω : ℝ)) :=
      (hξ.holdingTime k).coe_nnreal_real
    have h_cond_meas : MeasurableSet {ω | ξ.holdingTime k ω ≤ u} :=
      h_holding_meas measurableSet_Iic
    exact Measurable.aestronglyMeasurable (h_real_meas.indicator h_cond_meas)
  · filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact le_trans (abs_davisCappedRealizedResetIncrement_le S hflow ξ initial g C hg k u ω) (le_abs_self _)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The finite capped realized sum is bounded linearly in the number of
segments, uniformly in all duration caps. -/
theorem abs_davisFiniteCappedRealizedResetSum_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (cap : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) :
    |davisFiniteCappedRealizedResetSum
        S hflow ξ initial g cap N ω| ≤ (N : ℝ) * (2 * C) := by
  unfold davisFiniteCappedRealizedResetSum
  calc |∑ k ∈ Finset.range N, davisCappedRealizedResetIncrement S hflow ξ initial g k (cap k) ω|
      ≤ ∑ k ∈ Finset.range N, |davisCappedRealizedResetIncrement S hflow ξ initial g k (cap k) ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, (2 * C) := Finset.sum_le_sum fun k _ => abs_davisCappedRealizedResetIncrement_le S hflow ξ initial g C hg k (cap k) ω
    _ = N * (2 * C) := by simp [Finset.sum_const]

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Segmentwise occupation envelopes combine with the uniform realized-reset
bound to dominate the full finite occupation-centered sum. -/
theorem abs_davisFiniteCappedOccupationCenteredResetSum_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (cap : ℕ → ℝ≥0) (N : ℕ) (b : ℕ → Ω → ℝ)
    (hocc : ∀ k < N, ∀ ω,
      |davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k (cap k) ω| ≤ b k ω)
    (ω : Ω) :
    |davisFiniteCappedOccupationCenteredResetSum
        S hflow ξ initial g cap N ω| ≤
      (N : ℝ) * (2 * C) + ∑ k ∈ Finset.range N, b k ω := by
  unfold davisFiniteCappedOccupationCenteredResetSum
  have h1 : |davisFiniteCappedRealizedResetSum
      S hflow ξ initial g cap N ω - davisFiniteCappedResetOccupation
      S hflow g ξ initial cap N ω| ≤
      |davisFiniteCappedRealizedResetSum S hflow ξ initial g cap N ω| +
      |davisFiniteCappedResetOccupation S hflow g ξ initial cap N ω| :=
    abs_sub _ _
  calc |davisFiniteCappedRealizedResetSum S hflow ξ initial g cap N ω -
        davisFiniteCappedResetOccupation S hflow g ξ initial cap N ω|
      ≤ |davisFiniteCappedRealizedResetSum S hflow ξ initial g cap N ω| +
        |davisFiniteCappedResetOccupation S hflow g ξ initial cap N ω| := h1
    _ ≤ (N : ℝ) * (2 * C) + |davisFiniteCappedResetOccupation S hflow g ξ initial cap N ω| := by
        apply add_le_add_left
        exact abs_davisFiniteCappedRealizedResetSum_le S hflow ξ initial g C hg cap N ω
    _ ≤ (N : ℝ) * (2 * C) + ∑ k ∈ Finset.range N, b k ω := by
        apply add_le_add_right
        have h2 : |davisFiniteCappedResetOccupation S hflow g ξ initial cap N ω| ≤
            ∑ k ∈ Finset.range N, b k ω := by
          unfold davisFiniteCappedResetOccupation
          exact le_trans (Finset.abs_sum_le_sum_abs _ _)
            (Finset.sum_le_sum fun k hk => hocc k (Finset.mem_range.mp hk) ω)
        exact h2

/-- Integrable segmentwise occupation envelopes give integrability of the
finite capped occupation-centered sum. -/
theorem DavisJumpNoise.MeasurableNoise.integrable_finiteCappedOccupationCenteredResetSum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (hgmeas : Measurable g) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (cap : ℕ → ℝ≥0) (N : ℕ)
    (hocc : ∀ k < N, Integrable
      (davisCappedSampledResetOccupationCompensator
        S hflow g ξ initial k (cap k)) P) :
    Integrable (davisFiniteCappedOccupationCenteredResetSum
      S hflow ξ initial g cap N) P := by
  -- The centered sum is the realized sum minus the occupation sum
  unfold davisFiniteCappedOccupationCenteredResetSum
  -- Show each component is integrable
  have hreal : ∀ k < N, Integrable
      (davisCappedRealizedResetIncrement S hflow ξ initial g k (cap k)) P := by
    intro k hk
    exact hξ.integrable_cappedRealizedResetIncrement S hflow hf hr initial g hgmeas C hg k (cap k)
  have hrealInt : Integrable
      (davisFiniteCappedRealizedResetSum S hflow ξ initial g cap N) P := by
    unfold davisFiniteCappedRealizedResetSum
    exact integrable_finset_sum (Finset.range N) fun k hk => hreal k (Finset.mem_range.mp hk)
  have hoccInt : Integrable
      (davisFiniteCappedResetOccupation S hflow g ξ initial cap N) P := by
    unfold davisFiniteCappedResetOccupation
    exact integrable_finset_sum (Finset.range N) fun k hk => hocc k (Finset.mem_range.mp hk)
  exact hrealInt.sub hoccInt

end SHS
