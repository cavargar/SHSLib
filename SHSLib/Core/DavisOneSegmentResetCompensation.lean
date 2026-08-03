import SHSLib.Core.DavisConditionalHoldingMonotone

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Deterministic one-segment reset compensation

This module identifies the density obtained by weighting the normalized expected
reset increment by the holding-time hazard density.  Pointwise, it is exactly
the survivor-weighted reset part of the extended generator.  The corresponding
identity for integrals over a finite segment is then immediate.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Hazard-density-weighted normalized reset increment along one deterministic
Davis flow segment. -/
def davisSegmentExpectedResetDensity (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) (s : ℝ) : ℝ :=
  davisSegmentHazardDensity S hflow z s *
    davisExpectedResetIncrement S g
      (davisFlow S hflow s.toNNReal z)

/-- Survivor-weighted reset-generator density along one deterministic Davis
flow segment. -/
def davisSegmentResetGeneratorDensity (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) (s : ℝ) : ℝ :=
  Real.exp (-davisIntegratedHazard S hflow z s.toNNReal) *
    ∑ ℓ : Fin m,
      (g (S.resetDavisState ℓ (davisFlow S hflow s.toNNReal z)) -
        g (davisFlow S hflow s.toNNReal z)) *
      S.intensity ℓ
        (davisFlow S hflow s.toNNReal z).1
        (davisFlow S hflow s.toNNReal z).2.1
        (davisFlow S hflow s.toNNReal z).2.2

/-- The hazard-weighted expected reset increment is pointwise the
survivor-weighted reset part of the generator. -/
theorem davisSegmentExpectedResetDensity_eq_resetGeneratorDensity
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (z : DavisState Q n) (s : ℝ) :
    davisSegmentExpectedResetDensity S hflow g z s =
      davisSegmentResetGeneratorDensity S hflow g z s := by
  unfold davisSegmentExpectedResetDensity davisSegmentResetGeneratorDensity
  unfold davisSegmentHazardDensity
  have key := totalIntensity_mul_davisExpectedResetIncrement S g
    (davisFlow S hflow s.toNNReal z)
  rw [mul_comm (S.totalIntensity _) (Real.exp _), mul_assoc, key]

/-- Integral of the expected reset density over a segment of elapsed length
`u`. -/
def davisSegmentExpectedResetCompensator (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) (u : ℝ≥0) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
    davisSegmentExpectedResetDensity S hflow g z s

/-- The one-segment expected reset compensator is equivalently the integral of
the survivor-weighted reset-generator density. -/
theorem davisSegmentExpectedResetCompensator_eq_integral_resetGeneratorDensity
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (z : DavisState Q n) (u : ℝ≥0) :
    davisSegmentExpectedResetCompensator S hflow g z u =
      ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        davisSegmentResetGeneratorDensity S hflow g z s := by
  simp only [davisSegmentExpectedResetCompensator]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro s _
  exact davisSegmentExpectedResetDensity_eq_resetGeneratorDensity S hflow g z s

/-- For a bounded test function, the absolute expected-reset density is bounded
by twice the bound times the segment hazard density. -/
theorem abs_davisSegmentExpectedResetDensity_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (z : DavisState Q n) (s : ℝ) :
    |davisSegmentExpectedResetDensity S hflow g z s| ≤
      2 * C * davisSegmentHazardDensity S hflow z s := by
  unfold davisSegmentExpectedResetDensity
  rw [abs_mul]
  have hd_nonneg : 0 ≤ davisSegmentHazardDensity S hflow z s := by
    unfold davisSegmentHazardDensity
    exact mul_nonneg (totalIntensity_nonneg S _) (Real.exp_nonneg _)
  rw [abs_of_nonneg hd_nonneg]
  have hi_nonneg : 0 ≤ davisSegmentHazardDensity S hflow z s := hd_nonneg
  have grip_bound : |davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z)| ≤ 2 * C := by
    unfold davisExpectedResetIncrement
    set z' := davisFlow S hflow s.toNNReal z with hz'
    -- First show C ≥ 0
    have hC_nonneg : 0 ≤ C := by
      by_contra hC_neg
      push_neg at hC_neg
      have := hg (davisFlow S hflow s.toNNReal z)
      linarith [abs_nonneg (g (davisFlow S hflow s.toNNReal z))]
    -- Bound each term
    have hdiff_bound : ∀ ℓ, |g (S.resetDavisState ℓ z') - g z'| ≤ 2 * C := by
      intro ℓ
      calc |g (S.resetDavisState ℓ z') - g z'| ≤ |g (S.resetDavisState ℓ z')| + |g z'| := abs_sub _ _
        _ ≤ C + C := by apply add_le_add (hg _) (hg _)
        _ = 2 * C := by ring
    -- Use triangle inequality
    calc |∑ ℓ, S.davisChannelProbability z' ℓ * (g (S.resetDavisState ℓ z') - g z')|
        ≤ ∑ ℓ, |S.davisChannelProbability z' ℓ * (g (S.resetDavisState ℓ z') - g z')| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ ℓ, S.davisChannelProbability z' ℓ * |g (S.resetDavisState ℓ z') - g z'| := by
          congr 1; ext ℓ
          rw [abs_mul, abs_of_nonneg (davisChannelProbability_nonneg S z' ℓ)]
      _ ≤ ∑ ℓ, S.davisChannelProbability z' ℓ * (2 * C) := by
          apply Finset.sum_le_sum
          intro ℓ _
          exact mul_le_mul_of_nonneg_left (hdiff_bound ℓ) (davisChannelProbability_nonneg S z' ℓ)
      _ = 2 * C * ∑ ℓ, S.davisChannelProbability z' ℓ := by rw [Finset.mul_sum]; ac_rfl
      _ ≤ 2 * C * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith : 0 ≤ 2 * C)
          by_cases hz : S.totalIntensity z' = 0
          · -- When total intensity is 0, all probabilities are 0
            simp [davisChannelProbability, hz]
          · -- When total intensity > 0, sum is exactly 1
            rw [sum_davisChannelProbability S z' hz]
      _ = 2 * C := by ring
  calc S.davisSegmentHazardDensity hflow z s * |davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z)|
      ≤ S.davisSegmentHazardDensity hflow z s * (2 * C) := by apply mul_le_mul_of_nonneg_left grip_bound hi_nonneg
    _ = 2 * C * S.davisSegmentHazardDensity hflow z s := by ring

end SHS
