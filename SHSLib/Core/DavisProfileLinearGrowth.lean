import SHSLib.Core.DavisBoundedHazardVacuity

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Linear growth of the centered reset profile in the age

The uniform bound on the centered reset profile used so far rests on a hazard
that stays bounded as the age grows, which the previous module showed to be
incompatible with the conditional holding-time law.  What a bounded intensity
does give, with no further assumption, is a bound that grows *linearly* in the
age:

`|Φ(z, r)| ≤ 2·Cg + 2·Cg·Λ·r`.

Since every age that occurs before an observation time `T` is at most `T`, the
linear bound yields a uniform bound *below an age horizon*,

`|Φ(z, r)| ≤ 2·Cg·(1 + Λ·T)` for `r ≤ T`,

with a constant depending on the horizon.  These are the non-vacuous
replacements for the uniform bound: they follow from a bounded test function
and a bounded intensity alone.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- Under a uniform bound on the total intensity, the hazard accumulated along
the flow up to age `u` is at most that bound times `u`. -/
theorem davisIntegratedHazard_le_mul
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (Lam : ℝ) (hLam : ∀ z, S.totalIntensity z ≤ Lam)
    (z : DavisState Q n) (u : ℝ≥0) :
    davisIntegratedHazard S hflow z u ≤ Lam * (u : ℝ) := by
  unfold davisIntegratedHazard
  calc ∫ s in Set.Icc (0 : ℝ) (u : ℝ),
        S.totalIntensity (davisFlow S hflow s.toNNReal z)
      ≤ ∫ _ in Set.Icc (0 : ℝ) (u : ℝ), Lam := by
        refine setIntegral_mono_on ((hcont z).integrableOn_Icc)
          (integrable_const Lam) measurableSet_Icc fun s _ => hLam _
    _ = Lam * (u : ℝ) := by
        rw [setIntegral_const, smul_eq_mul, measureReal_def, Real.volume_Icc]
        simp [mul_comm]

/-- Under a bounded test function and a bounded intensity, the partial
occupation compensator grows at most linearly in the age. -/
theorem abs_davisSegmentResetOccupationCompensator_le_linear
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {g : DavisState Q n → ℝ}
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg)
    (Lam : ℝ) (hLam : ∀ z, S.totalIntensity z ≤ Lam)
    (z : DavisState Q n) (u : ℝ≥0) :
    |davisSegmentResetOccupationCompensator S hflow g z u| ≤
      2 * Cg * (Lam * (u : ℝ)) := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC (davisFlow S hflow 0 z))
  have hdensint : IntegrableOn
      (davisSegmentResetOccupationDensity S hflow g z)
      (Set.Icc (0 : ℝ) ((u : ℝ≥0) : ℝ)) :=
    ((hgcont z).continuousOn.integrableOn_compact isCompact_Icc)
  have hintint : IntegrableOn
      (fun s : ℝ => S.totalIntensity (davisFlow S hflow s.toNNReal z))
      (Set.Icc (0 : ℝ) ((u : ℝ≥0) : ℝ)) :=
    ((hcont z).continuousOn.integrableOn_compact isCompact_Icc)
  refine le_trans (abs_davisSegmentResetOccupationCompensator_le_integral_intensity
    S hflow g Cg hgC z u hdensint hintint) ?_
  exact mul_le_mul_of_nonneg_left
    (davisIntegratedHazard_le_mul S hflow hcont Lam hLam z u) (by positivity)

/-- **Linear growth of the centered reset profile.**  A bounded test function
and a bounded intensity give a profile bound that grows linearly in the age;
no bound on the accumulated hazard is needed. -/
theorem abs_davisSegmentCenteredResetProfile_le_linear
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {g : DavisState Q n → ℝ}
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg)
    (Lam : ℝ) (hLam : ∀ z, S.totalIntensity z ≤ Lam)
    (z : DavisState Q n) (r : ℝ) :
    |davisSegmentCenteredResetProfile S hflow g z r| ≤
      2 * Cg + 2 * Cg * (Lam * max r 0) := by
  have hE := abs_davisExpectedResetIncrement_le_all S g
    (davisFlow S hflow r.toNNReal z) Cg hgC
  have hC := abs_davisSegmentResetOccupationCompensator_le_linear S hflow hcont
    hgcont Cg hgC Lam hLam z r.toNNReal
  have hcast : ((r.toNNReal : ℝ≥0) : ℝ) = max r 0 := Real.coe_toNNReal' r
  rw [hcast] at hC
  unfold davisSegmentCenteredResetProfile
  calc |davisExpectedResetIncrement S g (davisFlow S hflow r.toNNReal z) -
        davisSegmentResetOccupationCompensator S hflow g z r.toNNReal|
      ≤ |davisExpectedResetIncrement S g (davisFlow S hflow r.toNNReal z)| +
        |davisSegmentResetOccupationCompensator S hflow g z r.toNNReal| :=
        abs_sub _ _
    _ ≤ 2 * Cg + 2 * Cg * (Lam * max r 0) := add_le_add hE hC

/-- **The profile bound below an age horizon.**  Below a horizon `T` the linear
bound becomes uniform, with the horizon-dependent constant `2·Cg·(1 + Λ·T)`. -/
theorem abs_davisSegmentCenteredResetProfile_le_of_age_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {g : DavisState Q n → ℝ}
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg)
    (Lam : ℝ) (hLam : ∀ z, S.totalIntensity z ≤ Lam)
    (T : ℝ) (hT : 0 ≤ T) (z : DavisState Q n) (r : ℝ) (hr : r ≤ T) :
    |davisSegmentCenteredResetProfile S hflow g z r| ≤
      2 * Cg * (1 + Lam * T) := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC (davisFlow S hflow 0 z))
  have hLam0 : 0 ≤ Lam := le_trans (totalIntensity_nonneg S z) (hLam z)
  have hmax : max r 0 ≤ T := max_le hr hT
  refine le_trans (abs_davisSegmentCenteredResetProfile_le_linear S hflow hcont
    hgcont Cg hgC Lam hLam z r) ?_
  have : Lam * max r 0 ≤ Lam * T := mul_le_mul_of_nonneg_left hmax hLam0
  nlinarith [hCg0, this]

end SHS
