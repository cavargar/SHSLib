import SHSLib.Core.DavisTwoChannelAgeTest
import SHSLib.Core.DavisAgeCounterMixedTest

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # A mixed test function on the two-channel refractory clock

This module puts the two mechanisms of the two-channel refractory clock into a
single Dynkin identity.  The test function is additively separable,

`g z = f (age z) + k (counter z)`,

with `f` an admissible age profile — bounded, Lipschitz, constant below the dead
time, continuously differentiable — and `k` an arbitrary bounded Lipschitz
profile of the counter.  Its compensator has both terms nonzero:

* the flow term `∫ f' (age)` accumulated while the clock ages, and
* the jump term averaging, over the two channels with weights `p` and `1 − p`,
  the increments `k (counter ± ρ(age)) − k (counter)`, whose size depends on the
  age at which the jump occurs.

The two mechanisms therefore interact: the deterministic ageing determines how
large the counter shift will be at the next reset.  The concrete instance takes
the flat ramp of `SHSLib.Core.DavisTwoChannelAgeTest` for the age and the cosine
for the counter, and needs no hypotheses beyond `0 < lam`, `0 < dd` and
`0 ≤ p ≤ 1`.
-/

namespace SHS

section TwoChannelMixed

variable {lam : ℝ} (hlam : 0 < lam) {dd : ℝ≥0} (hdd : 0 < dd) {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f f' k : ℝ → ℝ} {Cf Ck Lf Lk : ℝ}

include hlam hdd hp0 hp1

set_option maxHeartbeats 1000000 in
/-- **The Dynkin identity on the two-channel refractory clock for a mixed test
function.**  Both terms of the compensator are present: the flow term from the
age profile, the channel-dependent jump term from the counter profile. -/
theorem twoChannel_dynkin_mixedProfile (hfm : Measurable f) (hfc : Continuous f)
    (hCf : ∀ y, |f y| ≤ Cf) (hLf0 : 0 ≤ Lf)
    (hLf : ∀ y y' : ℝ, |f y - f y'| ≤ Lf * |y - y'|)
    (hflat : ∀ y : ℝ, y ≤ (dd : ℝ) → f y = f 0)
    (hderiv : ∀ y, HasDerivAt f (f' y) y) (hc' : Continuous f')
    (hkm : Measurable k) (hkc : Continuous k) (hCk : ∀ y, |k y| ≤ Ck)
    (hLk0 : 0 ≤ Lk) (hLk : ∀ y y' : ℝ, |k y - k y'| ≤ Lk * |y - y'|)
    (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (ageCounterAgeTest f') (ageCounterMixedTest f k) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 := by
  haveI : (twoChannelModel lam hlam dd p hp0 hp1).IntensitiesMeasurable :=
    twoChannel_intensitiesMeasurable hlam hp0 hp1
  have hfvanish : ∀ y, rampRate lam (dd : ℝ) y = 0 → f y = f 0 := fun y hy =>
    hflat y ((rampRate_eq_zero_iff hlam (dd : ℝ) y).mp hy)
  exact integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_boundedIntensity
    (hf := ageCounter_flowRegular _ _)
    (hr := ageCounter_resetRegular _ _ (twoShifts_measurable _))
    (hξ := twoChannelNoise_measurable lam dd)
    (twoChannel_nonExplosive hdd)
    (twoChannel_conditionalHoldingTimeLaw hlam hp0 hp1 t₀)
    (twoChannel_conditionalChannelLaw hlam hp0 hp1 t₀)
    (ageCounter_hazardContinuousAlongFlow _ _ (twoWeights_sum p)
      (continuous_rampRate lam (dd : ℝ)))
    (ageCounter_mixedResetOccupationContinuousAlongFlow _ _ (twoWeights_sum p)
      hfvanish (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)) hfc hkc
      (twoShifts_continuous (dd : ℝ)))
    (ageCounter_mixedResetOccupationRegular _ _ (twoWeights_sum p) hfvanish
      (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)).measurable
      (continuous_rampRate lam (dd : ℝ)) hfm hfc hkm hkc
      (twoShifts_measurable (dd : ℝ)) (twoShifts_continuous (dd : ℝ)))
    (measurable_ageCounterMixedTest hfm hkm) (Cf + Ck)
    (fun z => abs_ageCounterMixedTest_le hCf hCk z)
    (ageCounter_mixedExpectedResetIncrement_continuous _ _ (twoWeights_sum p)
      hfvanish (twoShifts_vanish hlam) hfc hkc (twoShifts_continuous (dd : ℝ)))
    lam (ageCounter_totalIntensity_le _ _ (twoWeights_sum p) (rampRate_le hlam.le _))
    (Lf + Lk * 1) (by nlinarith)
    (ageCounter_mixedExpectedResetIncrement_lipschitz _ _ (twoWeights_sum p)
      hfvanish (twoShifts_vanish hlam) hLf hLk0 hLk (twoShifts_lipschitz (dd : ℝ)))
    dd hdd (le_twoChannelNoise_holdingTime lam dd)
    (ageCounter_mixedFlowIntegralIdentity _ _ hderiv hc') t

set_option maxHeartbeats 1000000 in
/-- **The martingale property on the two-channel refractory clock for a mixed
test function.** -/
theorem twoChannel_martingale_mixedProfile (hfm : Measurable f) (hfc : Continuous f)
    (hCf : ∀ y, |f y| ≤ Cf) (hLf0 : 0 ≤ Lf)
    (hLf : ∀ y y' : ℝ, |f y - f y'| ≤ Lf * |y - y'|)
    (hflat : ∀ y : ℝ, y ≤ (dd : ℝ) → f y = f 0)
    (hderiv : ∀ y, HasDerivAt f (f' y) y) (hc' : Continuous f')
    (hkm : Measurable k) (hkc : Continuous k) (hCk : ∀ y, |k y| ≤ Ck)
    (hLk0 : 0 ≤ Lk) (hLk : ∀ y y' : ℝ, |k y - k y'| ≤ Lk * |y - y'|) (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (ageCounterAgeTest f') (ageCounterMixedTest f k))
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) := by
  haveI : (twoChannelModel lam hlam dd p hp0 hp1).IntensitiesMeasurable :=
    twoChannel_intensitiesMeasurable hlam hp0 hp1
  have hfvanish : ∀ y, rampRate lam (dd : ℝ) y = 0 → f y = f 0 := fun y hy =>
    hflat y ((rampRate_eq_zero_iff hlam (dd : ℝ) y).mp hy)
  exact martingale_davisElapsedCompensatedGeneratorProcess_markedJump_of_boundedIntensity
    (twoChannel_nonExplosive hdd)
    (twoChannel_conditionalHoldingTimeLaw hlam hp0 hp1 t₀)
    (twoChannel_conditionalChannelLaw hlam hp0 hp1 t₀)
    (ageCounter_hazardContinuousAlongFlow _ _ (twoWeights_sum p)
      (continuous_rampRate lam (dd : ℝ)))
    (ageCounter_mixedResetOccupationContinuousAlongFlow _ _ (twoWeights_sum p)
      hfvanish (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)) hfc hkc
      (twoShifts_continuous (dd : ℝ)))
    (ageCounter_mixedResetOccupationRegular _ _ (twoWeights_sum p) hfvanish
      (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)).measurable
      (continuous_rampRate lam (dd : ℝ)) hfm hfc hkm hkc
      (twoShifts_measurable (dd : ℝ)) (twoShifts_continuous (dd : ℝ)))
    (measurable_ageCounterMixedTest hfm hkm) (Cf + Ck)
    (fun z => abs_ageCounterMixedTest_le hCf hCk z)
    (ageCounter_mixedExpectedResetIncrement_continuous _ _ (twoWeights_sum p)
      hfvanish (twoShifts_vanish hlam) hfc hkc (twoShifts_continuous (dd : ℝ)))
    lam (ageCounter_totalIntensity_le _ _ (twoWeights_sum p) (rampRate_le hlam.le _))
    (Lf + Lk * 1) (by nlinarith)
    (ageCounter_mixedExpectedResetIncrement_lipschitz _ _ (twoWeights_sum p)
      hfvanish (twoShifts_vanish hlam) hLf hLk0 hLk (twoShifts_lipschitz (dd : ℝ)))
    dd hdd (le_twoChannelNoise_holdingTime lam dd)
    (ageCounter_mixedFlowIntegralIdentity _ _ hderiv hc')

/-- **The Dynkin identity for the flat ramp of the age plus the cosine of the
counter** on the two-channel refractory clock. -/
theorem twoChannel_dynkin_flatRampCos (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (ageCounterAgeTest (flatRampDeriv (dd : ℝ)))
      (ageCounterMixedTest (flatRamp (dd : ℝ)) Real.cos) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 :=
  twoChannel_dynkin_mixedProfile hlam hdd hp0 hp1 (measurable_flatRamp (dd : ℝ))
    (continuous_flatRamp (dd : ℝ)) (abs_flatRamp_le (dd : ℝ)) zero_le_one
    (flatRamp_lipschitz (dd : ℝ))
    (fun y hy => by
      rw [flatRamp_of_le hy, flatRamp_of_le (le_of_lt (by exact_mod_cast hdd))])
    (hasDerivAt_flatRamp (dd : ℝ)) (continuous_flatRampDeriv (dd : ℝ))
    Real.continuous_cos.measurable Real.continuous_cos
    (fun y => Real.abs_cos_le_one y) zero_le_one cos_lipschitz t₀ t

/-- **The martingale property for the flat ramp of the age plus the cosine of
the counter** on the two-channel refractory clock. -/
theorem twoChannel_martingale_flatRampCos (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (ageCounterAgeTest (flatRampDeriv (dd : ℝ)))
        (ageCounterMixedTest (flatRamp (dd : ℝ)) Real.cos))
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) :=
  twoChannel_martingale_mixedProfile hlam hdd hp0 hp1 (measurable_flatRamp (dd : ℝ))
    (continuous_flatRamp (dd : ℝ)) (abs_flatRamp_le (dd : ℝ)) zero_le_one
    (flatRamp_lipschitz (dd : ℝ))
    (fun y hy => by
      rw [flatRamp_of_le hy, flatRamp_of_le (le_of_lt (by exact_mod_cast hdd))])
    (hasDerivAt_flatRamp (dd : ℝ)) (continuous_flatRampDeriv (dd : ℝ))
    Real.continuous_cos.measurable Real.continuous_cos
    (fun y => Real.abs_cos_le_one y) zero_le_one cos_lipschitz t₀

end TwoChannelMixed

end SHS
