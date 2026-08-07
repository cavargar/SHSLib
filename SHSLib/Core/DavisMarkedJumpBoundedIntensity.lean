import SHSLib.Core.DavisMarkedJumpHorizonStepLaw
import SHSLib.Core.DavisSegmentProfileRegularity
import SHSLib.Core.DavisMarkedJumpGeneratorMartingale

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The model-level statements under a bounded intensity

The model-level Dynkin identity for the observation filtration of the marked
jump history was proved from four conditions on the model, one of which — a
uniformly bounded accumulated hazard along the flow — is incompatible with the
conditional holding-time law unless the measure vanishes.  The statement was
therefore satisfiable only for the zero measure.

The horizon-dependent form of the conditional step law removes that condition:
below an observation time a bounded intensity already bounds the centered reset
profile, by `2·Cg·(1 + Λ·t)`.  This module records the resulting non-vacuous
model-level statements — the conditional step law, the martingale property of
the occupation-compensated test-function process and the Dynkin identity — for
a Davis model whose noise satisfies the conditional holding-time and channel
laws, with a bounded measurable test function, a bounded intensity, a Lipschitz
expected reset increment along the flow, and holding times bounded away from
zero.  No hypothesis is made on the accumulated hazard.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The conditional step law from model-level regularity, without any
hypothesis on the accumulated hazard.**  A bounded test function, a bounded
intensity, a Lipschitz expected reset increment along the flow and the two
continuity conditions already in use give the conditional step law of the
one-segment martingale for the observation filtration of the marked jump
history.

This is the non-vacuous replacement for
`SHS.davisSegmentConditionalStepLaw_markedJump_of_modelRegularity`, whose
bounded accumulated hazard forces the zero measure. -/
theorem davisSegmentConditionalStepLaw_markedJump_of_boundedIntensity
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
    (N : ℕ) :
    DavisSegmentConditionalStepLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g
      N := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC initial)
  have hLam0 : 0 ≤ Lam := le_trans (totalIntensity_nonneg S initial) (hLam _)
  exact davisSegmentConditionalStepLaw_markedJump_boundedIntensity hne hlaw
    hchan hcont hgcont hreg hg Cg hgC Lam hLam
    (measurable_davisSegmentCenteredResetProfile S hflow hf hr hg hreg)
    (continuous_davisSegmentCenteredResetProfile S hflow hgcont hEcont)
    (Lg + 2 * Cg * Lam) (by positivity)
    (abs_davisSegmentCenteredResetProfile_sub_le S hflow hgcont Cg hgC Lam hLam
      Lg hLg0 hLg) N

set_option maxHeartbeats 1000000 in
/-- **The deterministic-cap increment law from model-level regularity, without
any hypothesis on the accumulated hazard.** -/
theorem davisStoppedElapsedOccupationIncrementLaw_markedJump_of_boundedIntensity
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
          Lg * |(u : ℝ) - (v : ℝ)|) :
    DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
  DavisStoppedElapsedOccupationIncrementLaw.of_conditional_step_laws hcont
    hgcont fun N =>
      davisSegmentConditionalStepLaw_markedJump_of_boundedIntensity hne hlaw
        hchan hcont hgcont hreg hg Cg hgC hEcont Lam hLam Lg hLg0 hLg N

set_option maxHeartbeats 1000000 in
/-- **The Dynkin identity for a genuine observation filtration under a bounded
intensity.**  For a Davis model whose noise satisfies the conditional
holding-time and channel laws, with a bounded measurable test function, a
bounded intensity, a Lipschitz expected reset increment along the flow and
holding times bounded away from zero, the occupation-compensated test-function
increment has zero mean at every elapsed time.

This is the non-vacuous replacement for
`SHS.integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_modelRegularity`:
the uniformly bounded accumulated hazard, which forces the zero measure, has
been removed. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_boundedIntensity
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise} (hne : ξ.NonExplosive)
    {initial : DavisState Q n} {a g : DavisState Q n → ℝ}
    (hholding : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
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
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (hga : DavisFlowIntegralIdentity S hflow g a) (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC initial)
  have hincr : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
    davisStoppedElapsedOccupationIncrementLaw_markedJump_of_boundedIntensity hne
      hholding hchan hcont hgcont hreg hg Cg hgC hEcont Lam hLam Lg hLg0 hLg
  have henv : ∀ s : ℝ≥0, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g s) P := fun s =>
    @integrable_davisElapsedOccupationEnvelope_of_bounded_regime Q _ _ n m S
      hflow hf hr g hreg hcont Cg hCg0 hgC Lam hLam Ω _ P _ ξ hξ hne d hdpos hd
      initial hg s
  exact @integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump
    Q _ _ n m S hflow hf hr a g hreg Ω _ P _ ξ hξ hne
    (ξ.positiveHoldingTimes_of_holdingTime_ge d hdpos hd) initial hg hga hincr
    henv t

set_option maxHeartbeats 1000000 in
/-- **The occupation-compensated test-function process is a martingale for the
observation filtration of the marked jump history**, under the same
model-level hypotheses, with no hypothesis on the accumulated hazard. -/
theorem martingale_davisElapsedCompensatedGeneratorProcess_markedJump_of_boundedIntensity
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise} (hne : ξ.NonExplosive)
    {initial : DavisState Q n} {a g : DavisState Q n → ℝ}
    (hholding : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
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
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (hga : DavisFlowIntegralIdentity S hflow g a) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g)
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) P := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC initial)
  have hincr : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
    davisStoppedElapsedOccupationIncrementLaw_markedJump_of_boundedIntensity hne
      hholding hchan hcont hgcont hreg hg Cg hgC hEcont Lam hLam Lg hLg0 hLg
  have henv : ∀ s : ℝ≥0, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g s) P := fun s =>
    @integrable_davisElapsedOccupationEnvelope_of_bounded_regime Q _ _ n m S
      hflow hf hr g hreg hcont Cg hCg0 hgC Lam hLam Ω _ P _ ξ hξ hne d hdpos hd
      initial hg s
  exact @martingale_davisElapsedCompensatedGeneratorProcess_markedJump
    Q _ _ n m S hflow hf hr a g hreg Ω _ P _ ξ hξ hne initial hg hga hincr henv

end SHS
