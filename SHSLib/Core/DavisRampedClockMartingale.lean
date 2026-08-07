import SHSLib.Core.DavisRampedClockNoise
import SHSLib.Core.DavisNonExplosiveLowerBound

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # The Dynkin identity and the martingale property on a concrete model

Everything the model-level statements of
`SHSLib.Core.DavisMarkedJumpBoundedIntensity` assume is now available for a
single genuine object:

* the model is the ramped refractory clock, whose intensity is continuous along
  the flow and bounded by `lam`;
* the noise is the inverse-transform noise on the path space, whose two
  conditional laws were proved in `SHSLib.Core.DavisRampedClockNoise` and whose
  holding times are at least the dead time `dd > 0` for every sample — so the
  jump times diverge and the process does not explode;
* the test function is the bump profile of the age, which is bounded by one,
  one-Lipschitz, constant where the rate vanishes, and has the bump itself as
  flow generator.

The two conclusions below are therefore statements about an object that is
known to exist, with no remaining hypotheses beyond `0 < lam` and `0 < dd`:
the occupation-compensated test-function increment has zero mean at every
elapsed time, and the compensated process is a martingale for the observation
filtration of the marked jump history.
-/

namespace SHS

section Ramped

variable {lam : ℝ} (hlam : 0 < lam) {dd : ℝ≥0} (hdd : 0 < dd)

include hdd in
/-- The ramped noise does not explode: its holding times are at least the dead
time. -/
theorem ramped_nonExplosive : (rampedNoise lam dd).NonExplosive :=
  DavisJumpNoise.nonExplosive_of_holdingTime_ge _ dd hdd
    (le_rampedNoise_holdingTime lam dd)

/-- The intensities of the ramped clock are measurable. -/
theorem ramped_intensitiesMeasurable :
    (ageClockSHS (rampRate lam (dd : ℝ)) (rampRate_nonneg hlam.le (dd : ℝ))).IntensitiesMeasurable :=
  ageClock_intensitiesMeasurable (rampRate_nonneg hlam.le (dd : ℝ))
    (continuous_rampRate lam (dd : ℝ)).measurable

/-- The test function of the ramped clock is measurable. -/
theorem measurable_rampedClockTest (d : ℝ) : Measurable (rampedClockTest d) :=
  measurable_ageTestFunction (continuous_rampProfile d).measurable

/-- The flow integral identity of the ramped clock and its test function. -/
theorem ramped_flowIntegralIdentity :
    DavisFlowIntegralIdentity (rampedModel lam hlam dd) (rampedModelFlow lam hlam dd)
      (rampedClockTest (dd : ℝ)) (rampedClockTestGenerator (dd : ℝ)) :=
  ageClock_flowIntegralIdentity (rampRate_nonneg hlam.le (dd : ℝ))
    (hasDerivAt_rampProfile (dd : ℝ)) (continuous_rampBump (dd : ℝ))

include hlam in
/-- Continuity of the reset occupation density of the ramped clock along the
flow. -/
theorem ramped_resetOccupationContinuousAlongFlow :
    DavisResetOccupationContinuousAlongFlow (rampedModel lam hlam dd)
      (rampedModelFlow lam hlam dd) (rampedClockTest (dd : ℝ)) :=
  ageClock_resetOccupationContinuousAlongFlow (rampRate_nonneg hlam.le (dd : ℝ))
    (rampProfile_vanish hlam dd.coe_nonneg) (continuous_rampRate lam (dd : ℝ))
    (continuous_rampProfile (dd : ℝ))

include hlam in
/-- Regularity of the reset occupation of the ramped clock. -/
theorem ramped_resetOccupationRegular :
    DavisResetOccupationRegular (rampedModel lam hlam dd) (rampedModelFlow lam hlam dd)
      (rampedClockTest (dd : ℝ)) :=
  ageClock_resetOccupationRegular (rampRate_nonneg hlam.le (dd : ℝ))
    (rampProfile_vanish hlam dd.coe_nonneg) (continuous_rampRate lam (dd : ℝ))
    (continuous_rampProfile (dd : ℝ))

set_option maxHeartbeats 1000000 in
include hlam hdd in
/-- **The Dynkin identity on the ramped refractory clock.**  For the bump
profile of the age as test function, the occupation-compensated increment has
zero mean at every elapsed time. -/
theorem ramped_integral_davisElapsedCompensatedGeneratorProcess_eq_zero
    (t₀ : ℝ) (t : ℝ≥0) :
    ∫ ω, davisElapsedCompensatedGeneratorProcess (rampedModel lam hlam dd)
      (rampedModelFlow lam hlam dd) (rampedNoise lam dd)
      (ramped_nonExplosive hdd) (rampedInitial t₀)
      (rampedClockTestGenerator (dd : ℝ)) (rampedClockTest (dd : ℝ)) t ω
      ∂unitExpPathMeasure = 0 := by
  haveI := ramped_intensitiesMeasurable hlam (dd := dd)
  haveI : (rampedModel lam hlam dd).IntensitiesMeasurable :=
    ramped_intensitiesMeasurable hlam (dd := dd)
  exact integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_boundedIntensity
    (hf := ageClock_flowRegular (rampRate lam (dd : ℝ)) (rampRate_nonneg hlam.le (dd : ℝ)))
    (hr := ageClock_resetRegular (rampRate lam (dd : ℝ)) (rampRate_nonneg hlam.le (dd : ℝ)))
    (hξ := rampedNoise_measurable lam dd)
    (ramped_nonExplosive hdd)
    (ramped_conditionalHoldingTimeLaw hlam dd t₀)
    (ramped_conditionalChannelLaw hlam dd t₀)
    (rampedClock_hazardContinuousAlongFlow hlam.le)
    (ramped_resetOccupationContinuousAlongFlow hlam)
    (ramped_resetOccupationRegular hlam)
    (measurable_rampedClockTest (dd : ℝ)) 1
    (fun z => abs_ageTestFunction_le (abs_rampProfile_le_one (dd : ℝ)) z)
    (ageClock_expectedResetIncrement_continuous (rampRate_nonneg hlam.le (dd : ℝ))
      (rampProfile_vanish hlam dd.coe_nonneg) (continuous_rampProfile (dd : ℝ)))
    lam (rampedClock_totalIntensity_le hlam.le) 1 zero_le_one
    (ageClock_expectedResetIncrement_lipschitz (rampRate_nonneg hlam.le (dd : ℝ))
      (rampProfile_vanish hlam dd.coe_nonneg) (rampProfile_lipschitz (dd : ℝ)))
    dd hdd (le_rampedNoise_holdingTime lam dd)
    (ramped_flowIntegralIdentity hlam) t

set_option maxHeartbeats 1000000 in
include hlam hdd in
/-- **The martingale property on the ramped refractory clock.**  The
occupation-compensated test-function process is a martingale for the
observation filtration of the marked jump history. -/
theorem ramped_martingale_davisElapsedCompensatedGeneratorProcess (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess (rampedModel lam hlam dd)
        (rampedModelFlow lam hlam dd) (rampedNoise lam dd)
        (ramped_nonExplosive hdd) (rampedInitial t₀)
        (rampedClockTestGenerator (dd : ℝ)) (rampedClockTest (dd : ℝ)))
      ((rampedNoise lam dd).markedJumpFiltration (rampedModel lam hlam dd)
        (rampedModelFlow lam hlam dd)
        (ageClock_flowRegular (rampRate lam (dd : ℝ)) (rampRate_nonneg hlam.le (dd : ℝ)))
        (ageClock_resetRegular (rampRate lam (dd : ℝ)) (rampRate_nonneg hlam.le (dd : ℝ)))
        (rampedNoise_measurable lam dd) (ramped_nonExplosive hdd) (rampedInitial t₀))
      unitExpPathMeasure := by
  haveI := ramped_intensitiesMeasurable hlam (dd := dd)
  haveI : (rampedModel lam hlam dd).IntensitiesMeasurable :=
    ramped_intensitiesMeasurable hlam (dd := dd)
  exact martingale_davisElapsedCompensatedGeneratorProcess_markedJump_of_boundedIntensity
    (ramped_nonExplosive hdd)
    (ramped_conditionalHoldingTimeLaw hlam dd t₀)
    (ramped_conditionalChannelLaw hlam dd t₀)
    (rampedClock_hazardContinuousAlongFlow hlam.le)
    (ramped_resetOccupationContinuousAlongFlow hlam)
    (ramped_resetOccupationRegular hlam)
    (measurable_rampedClockTest (dd : ℝ)) 1
    (fun z => abs_ageTestFunction_le (abs_rampProfile_le_one (dd : ℝ)) z)
    (ageClock_expectedResetIncrement_continuous (rampRate_nonneg hlam.le (dd : ℝ))
      (rampProfile_vanish hlam dd.coe_nonneg) (continuous_rampProfile (dd : ℝ)))
    lam (rampedClock_totalIntensity_le hlam.le) 1 zero_le_one
    (ageClock_expectedResetIncrement_lipschitz (rampRate_nonneg hlam.le (dd : ℝ))
      (rampProfile_vanish hlam dd.coe_nonneg) (rampProfile_lipschitz (dd : ℝ)))
    dd hdd (le_rampedNoise_holdingTime lam dd)
    (ramped_flowIntegralIdentity hlam)

end Ramped

end SHS
