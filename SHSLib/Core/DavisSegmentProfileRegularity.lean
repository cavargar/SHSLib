import SHSLib.Core.DavisMarkedJumpSegmentMartingale

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Instances of the centered reset profile regularity

The conditional law of the completed part, and everything built on it, assumes
four properties of the centered reset profile

`Φ(z, r) = E[Δg](φ_r z) − comp(z, r)`:

joint measurability, continuity in the age, a uniform Lipschitz bound in the
age, and a uniform bound.  This module derives all four from conditions on the
model rather than on the profile:

* the test function is bounded — then the normalized expected reset increment
  is bounded by twice that bound, and so is the reset part of the occupation
  density relative to the intensity;
* the intensity is bounded along the flow — then the occupation density is
  bounded, so the partial occupation compensator is Lipschitz in the age;
* the *total* hazard accumulated along the flow is bounded, uniformly in the
  state — this is what keeps the compensator, which is an integral over the
  whole elapsed age, bounded rather than merely linearly growing;
* the normalized expected reset increment is Lipschitz along the flow.

The two continuity conditions already used elsewhere (of the intensity and of
the occupation density along the flow) supply the integrability side
conditions, and the regularity package of the reset occupation supplies the
measurability ones.  The resulting constants are

`L = Lg + 2·Cg·Λ`,   `K = 2·Cg + 2·Cg·Hmax`.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Joint measurability and continuity -/

/-- The centered reset profile is jointly measurable in the state and the
age. -/
theorem measurable_davisSegmentCenteredResetProfile
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (hf : DavisFlowRegular S hflow)
    (hr : DavisResetRegular S) [S.IntensitiesMeasurable]
    {g : DavisState Q n → ℝ} (hg : Measurable g)
    (hreg : DavisResetOccupationRegular S hflow g) :
    Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentCenteredResetProfile S hflow g p.1 p.2 := by
  have htoNN : Measurable fun p : DavisState Q n × ℝ => (p.2).toNNReal :=
    measurable_real_toNNReal.comp measurable_snd
  have hflowm : Measurable fun p : DavisState Q n × ℝ =>
      davisFlow S hflow (p.2).toNNReal p.1 :=
    hf.measurable_joint.comp (htoNN.prodMk measurable_fst)
  unfold davisSegmentCenteredResetProfile
  exact ((measurable_davisExpectedResetIncrement S hr g hg).comp hflowm).sub
    (hreg.stoppedCompensator_measurable.comp (measurable_fst.prodMk htoNN))

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The centered reset profile is continuous in the age. -/
theorem continuous_davisSegmentCenteredResetProfile
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {g : DavisState Q n → ℝ}
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (hEcont : ∀ z : DavisState Q n,
      Continuous fun s : ℝ => davisExpectedResetIncrement S g
        (davisFlow S hflow s.toNNReal z))
    (z : DavisState Q n) :
    Continuous (davisSegmentCenteredResetProfile S hflow g z) := by
  unfold davisSegmentCenteredResetProfile
  exact (hEcont z).sub
    (continuous_davisSegmentResetOccupationCompensator S hflow g hgcont z)

/-! ## The compensator is Lipschitz in the age -/

/-- Under a bounded test function and a bounded intensity along the flow, the
partial occupation compensator is Lipschitz in the age. -/
theorem abs_davisSegmentResetOccupationCompensator_sub_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {g : DavisState Q n → ℝ}
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg) (Lam : ℝ)
    (hLam : ∀ z : DavisState Q n, S.totalIntensity z ≤ Lam)
    (z : DavisState Q n) (u v : ℝ≥0) :
    |davisSegmentResetOccupationCompensator S hflow g z u -
        davisSegmentResetOccupationCompensator S hflow g z v| ≤
      2 * Cg * Lam * |(u : ℝ) - (v : ℝ)| := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC (davisFlow S hflow 0 z))
  have hLam0 : 0 ≤ Lam :=
    le_trans (totalIntensity_nonneg S (davisFlow S hflow 0 z)) (hLam _)
  have hdens : Continuous (davisSegmentResetOccupationDensity S hflow g z) :=
    hgcont z
  have hdensb : ∀ s : ℝ,
      |davisSegmentResetOccupationDensity S hflow g z s| ≤ 2 * Cg * Lam := by
    intro s
    refine le_trans (abs_davisSegmentResetOccupationDensity_le S hflow g Cg hgC
      z s) ?_
    exact mul_le_mul_of_nonneg_left (hLam _) (by positivity)
  -- the compensator as an interval integral
  have hint : ∀ w : ℝ≥0, davisSegmentResetOccupationCompensator S hflow g z w =
      ∫ s in (0 : ℝ)..(w : ℝ), davisSegmentResetOccupationDensity S hflow g z
        s := by
    intro w
    rw [davisSegmentResetOccupationCompensator,
      intervalIntegral.integral_of_le w.coe_nonneg,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hint u, hint v]
  have hsub : (∫ s in (0 : ℝ)..(u : ℝ),
        davisSegmentResetOccupationDensity S hflow g z s) -
      (∫ s in (0 : ℝ)..(v : ℝ),
        davisSegmentResetOccupationDensity S hflow g z s) =
      ∫ s in (v : ℝ)..(u : ℝ),
        davisSegmentResetOccupationDensity S hflow g z s := by
    rw [intervalIntegral.integral_interval_sub_left
      (hdens.intervalIntegrable _ _) (hdens.intervalIntegrable _ _)]
  rw [hsub]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (v : ℝ)) (b := (u : ℝ))
    (f := davisSegmentResetOccupationDensity S hflow g z)
    (C := 2 * Cg * Lam) (fun s _ => by
      rw [Real.norm_eq_abs]
      exact hdensb s)
  rw [Real.norm_eq_abs] at hbound
  simpa [abs_sub_comm] using hbound

/-! ## The Lipschitz bound and the uniform bound on the profile -/

/-- Under a bounded test function, a bounded intensity along the flow and a
Lipschitz expected reset increment along the flow, the centered reset profile
is Lipschitz in the age with constant `Lg + 2·Cg·Λ`. -/
theorem abs_davisSegmentCenteredResetProfile_sub_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {g : DavisState Q n → ℝ}
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg) (Lam : ℝ)
    (hLam : ∀ z : DavisState Q n, S.totalIntensity z ≤ Lam)
    (Lg : ℝ) (hLg0 : 0 ≤ Lg)
    (hLg : ∀ (z : DavisState Q n) (u v : ℝ≥0),
      |davisExpectedResetIncrement S g (davisFlow S hflow u z) -
        davisExpectedResetIncrement S g (davisFlow S hflow v z)| ≤
          Lg * |(u : ℝ) - (v : ℝ)|)
    (z : DavisState Q n) (r r' : ℝ) :
    |davisSegmentCenteredResetProfile S hflow g z r -
        davisSegmentCenteredResetProfile S hflow g z r'| ≤
      (Lg + 2 * Cg * Lam) * |r - r'| := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC (davisFlow S hflow 0 z))
  have hLam0 : 0 ≤ Lam :=
    le_trans (totalIntensity_nonneg S (davisFlow S hflow 0 z)) (hLam _)
  have hage : |((r.toNNReal : ℝ≥0) : ℝ) - ((r'.toNNReal : ℝ≥0) : ℝ)| ≤
      |r - r'| := by
    have h1 : ((r.toNNReal : ℝ≥0) : ℝ) = max r 0 := Real.coe_toNNReal' r
    have h2 : ((r'.toNNReal : ℝ≥0) : ℝ) = max r' 0 := Real.coe_toNNReal' r'
    rw [h1, h2]
    exact abs_max_sub_max_le_abs r r' 0
  have hE := hLg z r.toNNReal r'.toNNReal
  have hC := abs_davisSegmentResetOccupationCompensator_sub_le S hflow hgcont
    Cg hgC Lam hLam z r.toNNReal r'.toNNReal
  have hE' : |davisExpectedResetIncrement S g
        (davisFlow S hflow r.toNNReal z) -
      davisExpectedResetIncrement S g (davisFlow S hflow r'.toNNReal z)| ≤
      Lg * |r - r'| :=
    le_trans hE (mul_le_mul_of_nonneg_left hage hLg0)
  have hC' : |davisSegmentResetOccupationCompensator S hflow g z r.toNNReal -
      davisSegmentResetOccupationCompensator S hflow g z r'.toNNReal| ≤
      2 * Cg * Lam * |r - r'| :=
    le_trans hC (mul_le_mul_of_nonneg_left hage (by positivity))
  unfold davisSegmentCenteredResetProfile
  calc |(davisExpectedResetIncrement S g (davisFlow S hflow r.toNNReal z) -
          davisSegmentResetOccupationCompensator S hflow g z r.toNNReal) -
        (davisExpectedResetIncrement S g (davisFlow S hflow r'.toNNReal z) -
          davisSegmentResetOccupationCompensator S hflow g z r'.toNNReal)|
      = |(davisExpectedResetIncrement S g (davisFlow S hflow r.toNNReal z) -
            davisExpectedResetIncrement S g (davisFlow S hflow r'.toNNReal z)) -
          (davisSegmentResetOccupationCompensator S hflow g z r.toNNReal -
            davisSegmentResetOccupationCompensator S hflow g z r'.toNNReal)| := by
        ring_nf
    _ ≤ |davisExpectedResetIncrement S g (davisFlow S hflow r.toNNReal z) -
            davisExpectedResetIncrement S g (davisFlow S hflow r'.toNNReal z)| +
          |davisSegmentResetOccupationCompensator S hflow g z r.toNNReal -
            davisSegmentResetOccupationCompensator S hflow g z r'.toNNReal| :=
        abs_sub _ _
    _ ≤ Lg * |r - r'| + 2 * Cg * Lam * |r - r'| := add_le_add hE' hC'
    _ = (Lg + 2 * Cg * Lam) * |r - r'| := by ring

/-- Under a bounded test function and a uniformly bounded total hazard along
the flow, the centered reset profile is bounded by `2·Cg·(1 + Hmax)`. -/
theorem abs_davisSegmentCenteredResetProfile_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {g : DavisState Q n → ℝ}
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg) (Hmax : ℝ)
    (hHmax : ∀ (z : DavisState Q n) (u : ℝ≥0),
      davisIntegratedHazard S hflow z u ≤ Hmax)
    (z : DavisState Q n) (r : ℝ) :
    |davisSegmentCenteredResetProfile S hflow g z r| ≤
      2 * Cg + 2 * Cg * Hmax := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC (davisFlow S hflow 0 z))
  have hE := abs_davisExpectedResetIncrement_le_all S g
    (davisFlow S hflow r.toNNReal z) Cg hgC
  have hdensint : IntegrableOn
      (davisSegmentResetOccupationDensity S hflow g z)
      (Set.Icc (0 : ℝ) ((r.toNNReal : ℝ≥0) : ℝ)) :=
    ((hgcont z).continuousOn.integrableOn_compact isCompact_Icc)
  have hintint : IntegrableOn
      (fun s : ℝ => S.totalIntensity (davisFlow S hflow s.toNNReal z))
      (Set.Icc (0 : ℝ) ((r.toNNReal : ℝ≥0) : ℝ)) :=
    ((hcont z).continuousOn.integrableOn_compact isCompact_Icc)
  have hC := abs_davisSegmentResetOccupationCompensator_le_integral_intensity S
    hflow g Cg hgC z r.toNNReal hdensint hintint
  have hCH : |davisSegmentResetOccupationCompensator S hflow g z r.toNNReal| ≤
      2 * Cg * Hmax := by
    refine le_trans hC ?_
    exact mul_le_mul_of_nonneg_left (hHmax z r.toNNReal) (by positivity)
  unfold davisSegmentCenteredResetProfile
  calc |davisExpectedResetIncrement S g (davisFlow S hflow r.toNNReal z) -
        davisSegmentResetOccupationCompensator S hflow g z r.toNNReal|
      ≤ |davisExpectedResetIncrement S g (davisFlow S hflow r.toNNReal z)| +
        |davisSegmentResetOccupationCompensator S hflow g z r.toNNReal| :=
        abs_sub _ _
    _ ≤ 2 * Cg + 2 * Cg * Hmax := add_le_add hE hCH

/-! ## The step law from model-level regularity -/

set_option maxHeartbeats 1000000 in
/-- **The conditional step law from model-level regularity.**  A bounded test
function, an intensity bounded and with bounded accumulated hazard along the
flow, a Lipschitz expected reset increment along the flow, and the two
continuity conditions already in use, give the conditional step law of the
one-segment martingale for the observation filtration of the marked jump
history.

Caveat: the bounded accumulated hazard `hHmax` is incompatible with the
conditional holding-time law `hlaw` unless the measure vanishes — see
`SHS.measure_eq_zero_of_conditionalHoldingTimeLaw_of_boundedHazard`.  The
statement is therefore only satisfiable for `P = 0`; the age-localized
hypotheses of `SHS.abs_davisSegmentCenteredResetProfile_le_of_age_le` are the
non-vacuous replacement, and the resulting form of this statement, with
`hHmax` deleted, is
`SHS.davisSegmentConditionalStepLaw_markedJump_of_boundedIntensity`. -/
theorem davisSegmentConditionalStepLaw_markedJump_of_modelRegularity
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise} (hne : ξ.NonExplosive)
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hchan : ξ.ConditionalChannelLaw S hflow P initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (hreg : DavisResetOccupationRegular S hflow g)
    (hg : Measurable g) (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg)
    (hEcont : ∀ z : DavisState Q n,
      Continuous fun s : ℝ => davisExpectedResetIncrement S g
        (davisFlow S hflow s.toNNReal z))
    (Lam : ℝ) (hLam : ∀ z : DavisState Q n, S.totalIntensity z ≤ Lam)
    (Lg : ℝ) (hLg0 : 0 ≤ Lg)
    (hLg : ∀ (z : DavisState Q n) (u v : ℝ≥0),
      |davisExpectedResetIncrement S g (davisFlow S hflow u z) -
        davisExpectedResetIncrement S g (davisFlow S hflow v z)| ≤
          Lg * |(u : ℝ) - (v : ℝ)|)
    (Hmax : ℝ) (hHmax : ∀ (z : DavisState Q n) (u : ℝ≥0),
      davisIntegratedHazard S hflow z u ≤ Hmax)
    (N : ℕ) :
    DavisSegmentConditionalStepLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g
      N := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC initial)
  have hLam0 : 0 ≤ Lam :=
    le_trans (totalIntensity_nonneg S initial) (hLam _)
  exact davisSegmentConditionalStepLaw_markedJump hne hlaw hchan hcont hgcont
    hreg hg Cg hgC
    (measurable_davisSegmentCenteredResetProfile S hflow hf hr hg hreg)
    (continuous_davisSegmentCenteredResetProfile S hflow hgcont hEcont)
    (Lg + 2 * Cg * Lam) (by positivity)
    (abs_davisSegmentCenteredResetProfile_sub_le S hflow hgcont Cg hgC Lam hLam
      Lg hLg0 hLg)
    (2 * Cg + 2 * Cg * Hmax)
    (abs_davisSegmentCenteredResetProfile_le S hflow hcont hgcont Cg hgC Hmax
      hHmax) N

end SHS
