import SHSLib.Core.DavisMarkedJumpBoundedIntensity
import SHSLib.Core.DavisElapsedAccumulatedHazardMeasurable

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The model-level statements with a random lower bound on the holding times

The model-level statements for the observation filtration of the marked jump
history ask for a *deterministic* strictly positive lower bound `d` on every
holding time.  That requirement enters only through the integrability of the
elapsed occupation envelope, where it is used to bound the number of completed
jumps by `t / d`; the relaxed regime already replaces it by a random bound
`d(ω) > 0` whose reciprocal is integrable.

This module runs the relaxed regime with the observation filtration: the
deterministic-cap increment law comes from the bounded intensity, the envelope
integrability from the random lower bound, and the two together give the
martingale property of the occupation-compensated test-function process and the
Dynkin identity.  The uniform intensity bound is retained — it is what bounds
the centered reset profile below an age horizon — but the holding times are now
only required to stay away from zero pathwise.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The occupation-compensated test-function process is a martingale for the
observation filtration of the marked jump history**, under a bounded test
function, a bounded intensity, a Lipschitz expected reset increment along the
flow, and holding times bounded below by a random strictly positive variable
whose reciprocal is integrable. -/
theorem martingale_davisElapsedCompensatedGeneratorProcess_markedJump_of_relaxedRegime
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
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hdint : ∀ t : ℝ≥0, Integrable (fun ω => (t : ℝ) / (d ω : ℝ)) P)
    (hga : DavisFlowIntegralIdentity S hflow g a) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess S hflow ξ hne initial a g)
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) P := by
  have hincr : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
    davisStoppedElapsedOccupationIncrementLaw_markedJump_of_boundedIntensity hne
      hholding hchan hcont hgcont hreg hg Cg hgC hEcont Lam hLam Lg hLg0 hLg
  have henv : ∀ s : ℝ≥0, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g s) P := fun s =>
    @integrable_davisElapsedOccupationEnvelope_of_relaxed_regime'
      Q _ _ n m S hflow hf hr g hreg hcont Cg hgC Ω _ P ξ hξ hne initial hg
      (fun _ => Lam) (fun _ _ _ => hLam _) (integrable_const Lam) d hdpos hd
      hdint s
  exact @martingale_davisElapsedCompensatedGeneratorProcess_markedJump
    Q _ _ n m S hflow hf hr a g hreg Ω _ P _ ξ hξ hne initial hg hga hincr henv

set_option maxHeartbeats 1000000 in
/-- **The Dynkin identity for the observation filtration of the marked jump
history**, under a bounded test function, a bounded intensity, a Lipschitz
expected reset increment along the flow, and holding times bounded below by a
random strictly positive variable whose reciprocal is integrable. -/
theorem integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_relaxedRegime
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
    (d : Ω → ℝ≥0) (hdpos : ∀ ω, 0 < d ω)
    (hd : ∀ i ω, d ω ≤ ξ.holdingTime i ω)
    (hdint : ∀ t : ℝ≥0, Integrable (fun ω => (t : ℝ) / (d ω : ℝ)) P)
    (hga : DavisFlowIntegralIdentity S hflow g a) (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess
      S hflow ξ hne initial a g t ω ∂P = 0 := by
  have hincr : DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
    davisStoppedElapsedOccupationIncrementLaw_markedJump_of_boundedIntensity hne
      hholding hchan hcont hgcont hreg hg Cg hgC hEcont Lam hLam Lg hLg0 hLg
  have henv : ∀ s : ℝ≥0, Integrable
      (davisElapsedOccupationEnvelope S hflow ξ hne initial g s) P := fun s =>
    @integrable_davisElapsedOccupationEnvelope_of_relaxed_regime'
      Q _ _ n m S hflow hf hr g hreg hcont Cg hgC Ω _ P ξ hξ hne initial hg
      (fun _ => Lam) (fun _ _ _ => hLam _) (integrable_const Lam) d hdpos hd
      hdint s
  exact @integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump
    Q _ _ n m S hflow hf hr a g hreg Ω _ P _ ξ hξ hne
    (fun k ω => lt_of_lt_of_le (hdpos ω) (hd k ω)) initial hg hga hincr henv t

end SHS
