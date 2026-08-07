import SHSLib.Core.DavisMarkedJumpObservable
import SHSLib.Core.DavisElapsedBoundedRegime

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The generator martingale for the marked jump filtration

With the deterministic-cap increment law and the observability of the elapsed
occupation both available for the observation filtration of the marked jump
history, the elapsed occupation theory can be run with that filtration in
place of the full-information one.  This module carries out the three
remaining steps:

* the elapsed occupation-centered reset process is a martingale for the
  observation filtration;
* so is the occupation-compensated test-function process, once the flow
  fundamental-theorem identity relates the test function to its flow
  derivative;
* hence the Dynkin-type identity: the occupation-compensated increment has
  zero mean at every elapsed time.

The last theorem states all of this at the level of the model: the conditional
holding-time and channel laws of the noise, a bounded test function, an
intensity that is bounded and accumulates bounded hazard along the flow, a
Lipschitz expected reset increment, and holding times bounded away from zero.
No hypothesis is imposed on the profile or on the filtration directly.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## The martingale property for the observation filtration -/

/-- The elapsed occupation-centered reset process is a martingale for the
marked jump filtration, given the increment law and an integrable envelope. -/
theorem martingale_davisElapsedOccupationCenteredResetProcess_markedJump
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {g : DavisState Q n → ℝ} (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) {hne : ξ.NonExplosive}
    (initial : DavisState Q n) (hg : Measurable g)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Martingale
      (davisElapsedOccupationCenteredResetProcess S hflow ξ hne initial g)
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) P :=
  @DavisStoppedElapsedOccupationIncrementLaw.martingale Q _ _ n m S hflow hf hr
    g hreg Ω _ P _ (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hξ
    hne initial hg
    (davisElapsedOccupationObservable_markedJump S hflow hf hr ξ hξ hne initial
      hg hreg)
    hlaw henv

/-- The occupation-compensated test-function process is a martingale for the
marked jump filtration. -/
theorem martingale_davisElapsedCompensatedGeneratorProcess_markedJump
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {a g : DavisState Q n → ℝ} (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) {hne : ξ.NonExplosive}
    (initial : DavisState Q n) (hg : Measurable g)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g)
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) P :=
  martingale_davisElapsedCompensatedGeneratorProcess S hflow P
    (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial a g hga
    (@martingale_davisElapsedOccupationCenteredResetProcess_markedJump
      Q _ _ n m S hflow hf hr g hreg Ω _ P _ ξ hξ hne initial hg hlaw henv)

/-! ## The Dynkin identity for the observation filtration -/

/-- **Dynkin-type identity for the marked jump filtration.**  The
occupation-compensated test-function increment has zero mean at every elapsed
time. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {a g : DavisState Q n → ℝ} (hreg : DavisResetOccupationRegular S hflow g)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} (hξ : ξ.MeasurableNoise) {hne : ξ.NonExplosive}
    (hpos : ξ.PositiveHoldingTimes)
    (initial : DavisState Q n) (hg : Measurable g)
    (hga : DavisFlowIntegralIdentity S hflow g a)
    (hlaw : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g)
    (henv : ∀ t, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g t) P)
    (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 :=
  integral_davisElapsedCompensatedGeneratorProcess_eq_zero S hflow P
    (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne hpos initial a g
    hga
    (@martingale_davisElapsedOccupationCenteredResetProcess_markedJump
      Q _ _ n m S hflow hf hr g hreg Ω _ P _ ξ hξ hne initial hg hlaw henv) t

/-! ## The model-level statement -/

set_option maxHeartbeats 1000000 in
/-- **The Dynkin identity for a genuine observation filtration, from
model-level hypotheses.**  For a Davis model whose noise satisfies the
conditional holding-time and channel laws, with a bounded measurable test
function, an intensity that is bounded and accumulates bounded hazard along the
flow, a Lipschitz expected reset increment, and holding times bounded away from
zero, the occupation-compensated test-function increment has zero mean at every
elapsed time — and the compensated process is a martingale for the observation
filtration of the marked jump history.

Caveat: the bounded accumulated hazard `hHmax` is incompatible with the
conditional holding-time law `hholding` unless the measure vanishes — see
`SHS.measure_eq_zero_of_conditionalHoldingTimeLaw_of_boundedHazard`.  The
non-vacuous replacement, with `hHmax` deleted, is
`SHS.integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_boundedIntensity`. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_modelRegularity
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
    (Hmax : ℝ) (hHmax : ∀ (z : DavisState Q n) (u : ℝ≥0),
      davisIntegratedHazard S hflow z u ≤ Hmax)
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (hga : DavisFlowIntegralIdentity S hflow g a) (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC initial)
  have hincr : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
    DavisStoppedElapsedOccupationIncrementLaw.of_conditional_step_laws hcont
      hgcont fun N =>
        davisSegmentConditionalStepLaw_markedJump_of_modelRegularity hne hholding
          hchan hcont hgcont hreg hg Cg hgC hEcont Lam hLam Lg hLg0 hLg Hmax
          hHmax N
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
/-- The compensated generator process is a martingale for the observation
filtration of the marked jump history, under the same model-level hypotheses.

Caveat: as above, `hHmax` forces the zero measure; the non-vacuous replacement
is
`SHS.martingale_davisElapsedCompensatedGeneratorProcess_markedJump_of_boundedIntensity`. -/
theorem martingale_davisElapsedCompensatedGeneratorProcess_markedJump_of_modelRegularity
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
    (Hmax : ℝ) (hHmax : ∀ (z : DavisState Q n) (u : ℝ≥0),
      davisIntegratedHazard S hflow z u ≤ Hmax)
    (d : ℝ≥0) (hdpos : 0 < d) (hd : ∀ i ω, d ≤ ξ.holdingTime i ω)
    (hga : DavisFlowIntegralIdentity S hflow g a) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g)
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) P := by
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC initial)
  have hincr : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
    DavisStoppedElapsedOccupationIncrementLaw.of_conditional_step_laws hcont
      hgcont fun N =>
        davisSegmentConditionalStepLaw_markedJump_of_modelRegularity hne hholding
          hchan hcont hgcont hreg hg Cg hgC hEcont Lam hLam Lg hLg0 hLg Hmax
          hHmax N
  have henv : ∀ s : ℝ≥0, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g s) P := fun s =>
    @integrable_davisElapsedOccupationEnvelope_of_bounded_regime Q _ _ n m S
      hflow hf hr g hreg hcont Cg hCg0 hgC Lam hLam Ω _ P _ ξ hξ hne d hdpos hd
      initial hg s
  exact @martingale_davisElapsedCompensatedGeneratorProcess_markedJump
    Q _ _ n m S hflow hf hr a g hreg Ω _ P _ ξ hξ hne initial hg hga hincr henv

end SHS
