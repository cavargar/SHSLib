import SHSLib.Core.DavisResetCompensatorBounds

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Reset occupation density and the endpoint/time bridge

The density used after averaging over a holding time contains a survivor factor.
The compensator accumulated on an actually occupied flow segment does not: it
uses total intensity times normalized expected reset increment, and is stopped
at the sampled holding time.  This module records that distinction and the
algebraic bridge between the two densities.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- Predictable reset density accumulated while a deterministic segment is
actually occupied. -/
def davisSegmentResetOccupationDensity (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) (s : ℝ) : ℝ :=
  S.totalIntensity (davisFlow S hflow s.toNNReal z) *
    davisExpectedResetIncrement S g (davisFlow S hflow s.toNNReal z)

/-- The occupation density is the finite-channel reset part of the extended
generator, before multiplication by a survivor probability. -/
theorem davisSegmentResetOccupationDensity_eq_sum
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (z : DavisState Q n) (s : ℝ) :
    davisSegmentResetOccupationDensity S hflow g z s =
      ∑ ℓ : Fin m,
        (g (S.resetDavisState ℓ (davisFlow S hflow s.toNNReal z)) -
          g (davisFlow S hflow s.toNNReal z)) *
        S.intensity ℓ
          (davisFlow S hflow s.toNNReal z).1
          (davisFlow S hflow s.toNNReal z).2.1
          (davisFlow S hflow s.toNNReal z).2.2 := by
  unfold davisSegmentResetOccupationDensity
  exact totalIntensity_mul_davisExpectedResetIncrement S g
    (davisFlow S hflow s.toNNReal z)

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Averaging occupation at elapsed time `s` against survival to `s` gives the
one-segment expected reset density from the preceding modules. -/
theorem davisSegmentExpectedResetDensity_eq_survivor_mul_occupation
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (z : DavisState Q n) (s : ℝ) :
    davisSegmentExpectedResetDensity S hflow g z s =
      Real.exp (-davisIntegratedHazard S hflow z s.toNNReal) *
        davisSegmentResetOccupationDensity S hflow g z s := by
  unfold davisSegmentExpectedResetDensity davisSegmentHazardDensity
  unfold davisSegmentResetOccupationDensity
  ring

/-- Reset compensator accumulated along the actually occupied part of one
segment, stopped at elapsed duration `u`. -/
def davisSegmentResetOccupationCompensator (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) (u : ℝ≥0) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
    davisSegmentResetOccupationDensity S hflow g z s

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The earlier deterministic expected-reset compensator is the
survivor-weighted integral of the occupation density. -/
theorem davisSegmentExpectedResetCompensator_eq_integral_survivor_mul_occupation
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (z : DavisState Q n) (u : ℝ≥0) :
    davisSegmentExpectedResetCompensator S hflow g z u =
      ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        Real.exp (-davisIntegratedHazard S hflow z s.toNNReal) *
          davisSegmentResetOccupationDensity S hflow g z s := by
  unfold davisSegmentExpectedResetCompensator
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro s _
  exact davisSegmentExpectedResetDensity_eq_survivor_mul_occupation
    S hflow g z s

/-- For bounded `g`, the raw occupation density is bounded by `2C` times the
total intensity.  Unlike the survivor-weighted density, its integral over a
deterministic interval need not have a cap independent of the interval. -/
theorem abs_davisSegmentResetOccupationDensity_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (z : DavisState Q n) (s : ℝ) :
    |davisSegmentResetOccupationDensity S hflow g z s| ≤
      2 * C * S.totalIntensity (davisFlow S hflow s.toNNReal z) := by
  rw [davisSegmentResetOccupationDensity_eq_sum S hflow g z s]
  calc |∑ ℓ, (g (S.resetDavisState ℓ (S.davisFlow hflow s.toNNReal z)) - g (S.davisFlow hflow s.toNNReal z)) * S.intensity ℓ (S.davisFlow hflow s.toNNReal z).1 (S.davisFlow hflow s.toNNReal z).2.1 (S.davisFlow hflow s.toNNReal z).2.2|
      ≤ ∑ ℓ, |(g (S.resetDavisState ℓ (S.davisFlow hflow s.toNNReal z)) - g (S.davisFlow hflow s.toNNReal z)) * S.intensity ℓ (S.davisFlow hflow s.toNNReal z).1 (S.davisFlow hflow s.toNNReal z).2.1 (S.davisFlow hflow s.toNNReal z).2.2| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ℓ, |g (S.resetDavisState ℓ (S.davisFlow hflow s.toNNReal z)) - g (S.davisFlow hflow s.toNNReal z)| * S.intensity ℓ (S.davisFlow hflow s.toNNReal z).1 (S.davisFlow hflow s.toNNReal z).2.1 (S.davisFlow hflow s.toNNReal z).2.2 := by
        congr 1 with ℓ
        rw [abs_mul, abs_of_nonneg (S.intensity_nonneg ℓ _ _ _)]
    _ ≤ ∑ ℓ, 2 * C * S.intensity ℓ (S.davisFlow hflow s.toNNReal z).1 (S.davisFlow hflow s.toNNReal z).2.1 (S.davisFlow hflow s.toNNReal z).2.2 := by
        apply Finset.sum_le_sum
        intro ℓ _
        apply mul_le_mul_of_nonneg_right
        · calc |g (S.resetDavisState ℓ (S.davisFlow hflow s.toNNReal z)) - g (S.davisFlow hflow s.toNNReal z)|
              ≤ |g (S.resetDavisState ℓ (S.davisFlow hflow s.toNNReal z))| + |g (S.davisFlow hflow s.toNNReal z)| := abs_sub _ _
            _ ≤ C + C := add_le_add (hg _) (hg _)
            _ = 2 * C := by ring
        · exact S.intensity_nonneg ℓ _ _ _
    _ = 2 * C * S.totalIntensity (S.davisFlow hflow s.toNNReal z) := by
        rw [totalIntensity, Finset.mul_sum]

/-- The stopped occupation compensator is controlled by the accumulated total
hazard on the occupied interval. -/
theorem abs_davisSegmentResetOccupationCompensator_le_integral_intensity
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (C : ℝ) (hg : ∀ y, |g y| ≤ C)
    (z : DavisState Q n) (u : ℝ≥0)
    (hreset : IntegrableOn
      (davisSegmentResetOccupationDensity S hflow g z)
      (Set.Icc (0 : ℝ) (u : ℝ)))
    (hintensity : IntegrableOn
      (fun s : ℝ => S.totalIntensity (davisFlow S hflow s.toNNReal z))
      (Set.Icc (0 : ℝ) (u : ℝ))) :
    |davisSegmentResetOccupationCompensator S hflow g z u| ≤
      2 * C * ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        S.totalIntensity (davisFlow S hflow s.toNNReal z) := by
  unfold davisSegmentResetOccupationCompensator
  calc |∫ s in Set.Icc (0 : ℝ) (u : ℝ),
          davisSegmentResetOccupationDensity S hflow g z s|
      ≤ ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
          |davisSegmentResetOccupationDensity S hflow g z s| := by
        apply abs_integral_le_integral_abs
    _ ≤ ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
          2 * C * S.totalIntensity (davisFlow S hflow s.toNNReal z) := by
        apply MeasureTheory.setIntegral_mono_on
        · exact hreset.norm
        · apply MeasureTheory.Integrable.const_mul
          exact hintensity
        · exact measurableSet_Icc
        · intro s hs
          exact abs_davisSegmentResetOccupationDensity_le S hflow g C hg _ _
    _ = 2 * C * ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
          S.totalIntensity (davisFlow S hflow s.toNNReal z) := by
        rw [MeasureTheory.integral_const_mul]

end SHS
