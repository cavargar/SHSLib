import SHSLib.Core.DavisOneSegmentResetCompensation

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Integrated and finite-cap reset-compensator bounds

This module lifts the pointwise one-segment reset-density estimate to its
integral and then to a deterministic number of completed flow segments.  The
integrability assumptions are explicit, so the results can be reused before a
particular measurable Davis realization is fixed.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The absolute one-segment expected reset compensator is bounded by the
integral of twice the test-function bound times the hazard density. -/
theorem abs_davisSegmentExpectedResetCompensator_le_integral_hazardDensity
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (C : ℝ)
    (hg : ∀ y, |g y| ≤ C) (z : DavisState Q n) (u : ℝ≥0)
    (hreset : IntegrableOn
      (davisSegmentExpectedResetDensity S hflow g z)
      (Set.Icc (0 : ℝ) (u : ℝ)))
    (hhazard : IntegrableOn
      (davisSegmentHazardDensity S hflow z)
      (Set.Icc (0 : ℝ) (u : ℝ))) :
    |davisSegmentExpectedResetCompensator S hflow g z u| ≤
      2 * C * ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentHazardDensity S hflow z s := by
  unfold davisSegmentExpectedResetCompensator
  calc |∫ s in Set.Icc (0 : ℝ) (u : ℝ), davisSegmentExpectedResetDensity S hflow g z s|
      ≤ ∫ s in Set.Icc (0 : ℝ) (u : ℝ), |davisSegmentExpectedResetDensity S hflow g z s| :=
        MeasureTheory.norm_integral_le_integral_norm (davisSegmentExpectedResetDensity S hflow g z)
    _ ≤ ∫ s in Set.Icc (0 : ℝ) (u : ℝ), 2 * C * davisSegmentHazardDensity S hflow z s := by
        refine MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Icc ?_
        · exact hreset.norm
        · exact hhazard.const_mul (2 * C)
        · intro s _
          exact abs_davisSegmentExpectedResetDensity_le S hflow g C hg z s
    _ = 2 * C * ∫ s in Set.Icc (0 : ℝ) (u : ℝ), davisSegmentHazardDensity S hflow z s := by
        rw [integral_const_mul]

/-- With continuous hazard along deterministic flow, the integrated bound is
`2C` times the probability of a jump before the segment endpoint. -/
theorem abs_davisSegmentExpectedResetCompensator_le_survivor_loss
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ) (C : ℝ)
    (hg : ∀ y, |g y| ≤ C) (z : DavisState Q n) (u : ℝ≥0)
    (hreset : IntegrableOn
      (davisSegmentExpectedResetDensity S hflow g z)
      (Set.Icc (0 : ℝ) (u : ℝ)))
    (hhazard : IntegrableOn
      (davisSegmentHazardDensity S hflow z)
      (Set.Icc (0 : ℝ) (u : ℝ))) :
    |davisSegmentExpectedResetCompensator S hflow g z u| ≤
      2 * C * (1 - davisSegmentSurvivor S hflow z u) := by
  have h1 := abs_davisSegmentExpectedResetCompensator_le_integral_hazardDensity
    S hflow g C hg z u hreset hhazard
  rw [integral_davisSegmentHazardDensity S hflow hcont z u] at h1
  exact h1

/-- In particular, every integrable one-segment expected reset compensator is
bounded in absolute value by `2C`. -/
theorem abs_davisSegmentExpectedResetCompensator_le_two_mul
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ y, |g y| ≤ C) (z : DavisState Q n) (u : ℝ≥0)
    (hreset : IntegrableOn
      (davisSegmentExpectedResetDensity S hflow g z)
      (Set.Icc (0 : ℝ) (u : ℝ)))
    (hhazard : IntegrableOn
      (davisSegmentHazardDensity S hflow z)
      (Set.Icc (0 : ℝ) (u : ℝ))) :
    |davisSegmentExpectedResetCompensator S hflow g z u| ≤ 2 * C := by
  have h1 := abs_davisSegmentExpectedResetCompensator_le_survivor_loss
    S hflow hcont g C hg z u hreset hhazard
  have h2 : davisSegmentSurvivor S hflow z u ≤ 1 := davisSegmentSurvivor_le_one S hflow z u
  have h2p : 0 < davisSegmentSurvivor S hflow z u := davisSegmentSurvivor_pos S hflow z u
  have h3 : 1 - davisSegmentSurvivor S hflow z u ≤ 1 := by linarith
  have h4 : 2 * C * (1 - davisSegmentSurvivor S hflow z u) ≤ 2 * C := by nlinarith
  linarith

/-- Sum of one-segment expected reset compensators over the first `N`
completed deterministic segments. -/
def davisFiniteExpectedResetTimeCompensator (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ)
    (N : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    davisSegmentExpectedResetCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial k ω) (ξ.holdingTime k ω)

/-- A deterministic `N`-jump cap gives the uniform bound `N · 2C` for the
finite time-integrated reset compensator. -/
theorem abs_davisFiniteExpectedResetTimeCompensator_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    {Ω : Type*} (ξ : DavisJumpNoise m Ω) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ y, |g y| ≤ C) (N : ℕ) (ω : Ω)
    (hreset : ∀ k < N, IntegrableOn
      (davisSegmentExpectedResetDensity S hflow g
        (davisStateAfterJump S hflow ξ initial k ω))
      (Set.Icc (0 : ℝ) (ξ.holdingTime k ω : ℝ)))
    (hhazard : ∀ k < N, IntegrableOn
      (davisSegmentHazardDensity S hflow
        (davisStateAfterJump S hflow ξ initial k ω))
      (Set.Icc (0 : ℝ) (ξ.holdingTime k ω : ℝ))) :
    |davisFiniteExpectedResetTimeCompensator S hflow ξ initial g N ω| ≤
      (N : ℝ) * (2 * C) := by
  unfold davisFiniteExpectedResetTimeCompensator
  have hle : ∀ k < N, |davisSegmentExpectedResetCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial k ω) (ξ.holdingTime k ω)| ≤ 2 * C := by
    intro k hk
    exact abs_davisSegmentExpectedResetCompensator_le_two_mul S hflow hcont g C hC hg
      (davisStateAfterJump S hflow ξ initial k ω) (ξ.holdingTime k ω)
      (hreset k hk) (hhazard k hk)
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  calc ∑ k ∈ Finset.range N, |davisSegmentExpectedResetCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial k ω) (ξ.holdingTime k ω)|
      ≤ ∑ k ∈ Finset.range N, (2 * C) := Finset.sum_le_sum fun k hk => hle k (Finset.mem_range.mp hk)
      _ = N * (2 * C) := by simp [Finset.sum_const, nsmul_eq_mul]

end SHS
