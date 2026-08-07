import SHSLib.Core.DavisTwoChannelMixedTest
import SHSLib.Core.DavisAgeCounterJointTest

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # A joint test function on the two-channel refractory clock

The test functions available on the two-channel refractory clock so far are
separable: a profile of the age, a profile of the counter, or their sum.  This
module removes that restriction and runs the Dynkin identity and the martingale
property for a genuinely *joint* test function

`g z = h (age z) (counter z)`,

with `h : ℝ → ℝ → ℝ` arbitrary subject to regularity.  The hypotheses are the
two-dimensional ones of `SHSLib.Core.DavisAgeCounterJointTest`: joint
measurability and joint continuity, a uniform bound, a Lipschitz bound in the
counter at age zero (the only age at which a reset perturbs the counter, since
every reset zeroes the age), a Lipschitz bound in the age, flatness of `h` in
the age below the dead time, and a partial derivative in the age with jointly
continuous derivative.

The concrete instance is the non-separable amplitude-modulated cosine

`h a c = (1 + flatRamp dd a) · cos c`,

for which the age genuinely modulates the amplitude of the counter oscillation:
right after a reset the profile is `cos c`, and as the clock ages towards the
next reset the amplitude grows towards `2 cos c`.  It satisfies all the
hypotheses with `C = 2` and Lipschitz constants `L₁ = L₂ = 1`, so it needs no
hypotheses beyond `0 < lam`, `0 < dd` and `0 ≤ p ≤ 1`.
-/

namespace SHS

section RampCosProfile

/-! ## The amplitude-modulated cosine -/

/-- The non-separable profile `h a c = (1 + flatRamp d a) · cos c`: the age
modulates the amplitude of the counter oscillation. -/
def rampCosProfile (d : ℝ) : ℝ → ℝ → ℝ := fun a c => (1 + flatRamp d a) * Real.cos c

/-- Its partial derivative in the age. -/
def rampCosProfileDeriv (d : ℝ) : ℝ → ℝ → ℝ := fun a c => flatRampDeriv d a * Real.cos c

theorem continuous_rampCosProfile (d : ℝ) :
    Continuous (Function.uncurry (rampCosProfile d)) :=
  (continuous_const.add ((continuous_flatRamp d).comp continuous_fst)).mul
    (Real.continuous_cos.comp continuous_snd)

theorem measurable_rampCosProfile (d : ℝ) :
    Measurable (Function.uncurry (rampCosProfile d)) :=
  (continuous_rampCosProfile d).measurable

theorem continuous_rampCosProfileDeriv (d : ℝ) :
    Continuous (Function.uncurry (rampCosProfileDeriv d)) :=
  ((continuous_flatRampDeriv d).comp continuous_fst).mul
    (Real.continuous_cos.comp continuous_snd)

theorem abs_rampCosProfile_le (d : ℝ) (a c : ℝ) : |rampCosProfile d a c| ≤ 2 := by
  have h1 : |1 + flatRamp d a| ≤ 2 := by
    have := abs_flatRamp_le d a
    have h2 := abs_le.mp this
    rw [abs_le]
    constructor <;> linarith [h2.1, h2.2]
  have h2 : |Real.cos c| ≤ 1 := Real.abs_cos_le_one c
  calc |rampCosProfile d a c| = |1 + flatRamp d a| * |Real.cos c| := by
        rw [rampCosProfile, abs_mul]
    _ ≤ 2 * 1 := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = 2 := by norm_num

theorem rampCosProfile_zero_age {d : ℝ} (hd : 0 ≤ d) (c : ℝ) :
    rampCosProfile d 0 c = Real.cos c := by
  rw [rampCosProfile, flatRamp_of_le hd]
  ring

/-- Flatness below the dead time: the profile does not depend on the age there. -/
theorem rampCosProfile_flat {d : ℝ} (hd : 0 ≤ d) (a : ℝ) (ha : a ≤ d) (c : ℝ) :
    rampCosProfile d a c = rampCosProfile d 0 c := by
  rw [rampCosProfile, rampCosProfile, flatRamp_of_le ha, flatRamp_of_le hd]

/-- Lipschitz in the counter at age zero, with constant one. -/
theorem rampCosProfile_lipschitz_counter {d : ℝ} (hd : 0 ≤ d) (c c' : ℝ) :
    |rampCosProfile d 0 c - rampCosProfile d 0 c'| ≤ 1 * |c - c'| := by
  rw [rampCosProfile_zero_age hd, rampCosProfile_zero_age hd]
  exact cos_lipschitz c c'

/-- Lipschitz in the age, with constant one. -/
theorem rampCosProfile_lipschitz_age (d a a' c : ℝ) :
    |rampCosProfile d a c - rampCosProfile d a' c| ≤ 1 * |a - a'| := by
  have hfact : rampCosProfile d a c - rampCosProfile d a' c
      = (flatRamp d a - flatRamp d a') * Real.cos c := by
    rw [rampCosProfile, rampCosProfile]; ring
  have hcos : |Real.cos c| ≤ 1 := Real.abs_cos_le_one c
  calc |rampCosProfile d a c - rampCosProfile d a' c|
      = |flatRamp d a - flatRamp d a'| * |Real.cos c| := by rw [hfact, abs_mul]
    _ ≤ (1 * |a - a'|) * 1 :=
        mul_le_mul (flatRamp_lipschitz d a a') hcos (abs_nonneg _) (by positivity)
    _ = 1 * |a - a'| := by ring

theorem hasDerivAt_rampCosProfile (d a c : ℝ) :
    HasDerivAt (fun x => rampCosProfile d x c) (rampCosProfileDeriv d a c) a := by
  simpa [rampCosProfile, rampCosProfileDeriv] using
    ((hasDerivAt_flatRamp d a).const_add 1).mul_const (Real.cos c)

end RampCosProfile

section TwoChannelJoint

variable {lam : ℝ} (hlam : 0 < lam) {dd : ℝ≥0} (hdd : 0 < dd) {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {h h' : ℝ → ℝ → ℝ} {C L1 L2 : ℝ}

include hlam hdd hp0 hp1

set_option maxHeartbeats 1000000 in
/-- **The Dynkin identity on the two-channel refractory clock for a joint test
function.**  Nothing about the compensator splits into an age part and a counter
part: the jump term averages, over the two channels, increments in which the
shift of the counter is a function of the age at which the jump occurs. -/
theorem twoChannel_dynkin_jointProfile (hm : Measurable (Function.uncurry h))
    (hcont : Continuous (Function.uncurry h)) (hC : ∀ a c, |h a c| ≤ C)
    (hL1' : 0 ≤ L1) (hL1 : ∀ c c' : ℝ, |h 0 c - h 0 c'| ≤ L1 * |c - c'|)
    (hL2' : 0 ≤ L2) (hL2 : ∀ a a' c : ℝ, |h a c - h a' c| ≤ L2 * |a - a'|)
    (hflat : ∀ a : ℝ, a ≤ (dd : ℝ) → ∀ c, h a c = h 0 c)
    (hderiv : ∀ a c, HasDerivAt (fun x => h x c) (h' a c) a)
    (hc' : Continuous (Function.uncurry h'))
    (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (ageCounterJointTest h') (ageCounterJointTest h) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 := by
  haveI : (twoChannelModel lam hlam dd p hp0 hp1).IntensitiesMeasurable :=
    twoChannel_intensitiesMeasurable hlam hp0 hp1
  have hvanish : ∀ a, rampRate lam (dd : ℝ) a = 0 → ∀ c, h a c = h 0 c := fun a ha =>
    hflat a ((rampRate_eq_zero_iff hlam (dd : ℝ) a).mp ha)
  exact integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_boundedIntensity
    (hf := ageCounter_flowRegular _ _)
    (hr := ageCounter_resetRegular _ _ (twoShifts_measurable _))
    (hξ := twoChannelNoise_measurable lam dd)
    (twoChannel_nonExplosive hdd)
    (twoChannel_conditionalHoldingTimeLaw hlam hp0 hp1 t₀)
    (twoChannel_conditionalChannelLaw hlam hp0 hp1 t₀)
    (ageCounter_hazardContinuousAlongFlow _ _ (twoWeights_sum p)
      (continuous_rampRate lam (dd : ℝ)))
    (ageCounter_jointResetOccupationContinuousAlongFlow _ _ (twoWeights_sum p)
      hvanish (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)) hcont
      (twoShifts_continuous (dd : ℝ)))
    (ageCounter_jointResetOccupationRegular _ _ (twoWeights_sum p) hvanish
      (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)).measurable
      (continuous_rampRate lam (dd : ℝ)) hm hcont
      (twoShifts_measurable (dd : ℝ)) (twoShifts_continuous (dd : ℝ)))
    (measurable_ageCounterJointTest hm) C
    (fun z => abs_ageCounterJointTest_le hC z)
    (ageCounter_jointExpectedResetIncrement_continuous _ _ (twoWeights_sum p)
      hvanish (twoShifts_vanish hlam) hcont (twoShifts_continuous (dd : ℝ)))
    lam (ageCounter_totalIntensity_le _ _ (twoWeights_sum p) (rampRate_le hlam.le _))
    (L1 * 1 + L2) (by nlinarith)
    (ageCounter_jointExpectedResetIncrement_lipschitz _ _ (twoWeights_sum p)
      hvanish (twoShifts_vanish hlam) hL1' hL1 hL2 (twoShifts_lipschitz (dd : ℝ)))
    dd hdd (le_twoChannelNoise_holdingTime lam dd)
    (ageCounter_jointFlowIntegralIdentity _ _ hderiv hc') t

set_option maxHeartbeats 1000000 in
/-- **The martingale property on the two-channel refractory clock for a joint
test function.** -/
theorem twoChannel_martingale_jointProfile (hm : Measurable (Function.uncurry h))
    (hcont : Continuous (Function.uncurry h)) (hC : ∀ a c, |h a c| ≤ C)
    (hL1' : 0 ≤ L1) (hL1 : ∀ c c' : ℝ, |h 0 c - h 0 c'| ≤ L1 * |c - c'|)
    (hL2' : 0 ≤ L2) (hL2 : ∀ a a' c : ℝ, |h a c - h a' c| ≤ L2 * |a - a'|)
    (hflat : ∀ a : ℝ, a ≤ (dd : ℝ) → ∀ c, h a c = h 0 c)
    (hderiv : ∀ a c, HasDerivAt (fun x => h x c) (h' a c) a)
    (hc' : Continuous (Function.uncurry h')) (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (ageCounterJointTest h') (ageCounterJointTest h))
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
  have hvanish : ∀ a, rampRate lam (dd : ℝ) a = 0 → ∀ c, h a c = h 0 c := fun a ha =>
    hflat a ((rampRate_eq_zero_iff hlam (dd : ℝ) a).mp ha)
  exact martingale_davisElapsedCompensatedGeneratorProcess_markedJump_of_boundedIntensity
    (twoChannel_nonExplosive hdd)
    (twoChannel_conditionalHoldingTimeLaw hlam hp0 hp1 t₀)
    (twoChannel_conditionalChannelLaw hlam hp0 hp1 t₀)
    (ageCounter_hazardContinuousAlongFlow _ _ (twoWeights_sum p)
      (continuous_rampRate lam (dd : ℝ)))
    (ageCounter_jointResetOccupationContinuousAlongFlow _ _ (twoWeights_sum p)
      hvanish (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)) hcont
      (twoShifts_continuous (dd : ℝ)))
    (ageCounter_jointResetOccupationRegular _ _ (twoWeights_sum p) hvanish
      (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)).measurable
      (continuous_rampRate lam (dd : ℝ)) hm hcont
      (twoShifts_measurable (dd : ℝ)) (twoShifts_continuous (dd : ℝ)))
    (measurable_ageCounterJointTest hm) C
    (fun z => abs_ageCounterJointTest_le hC z)
    (ageCounter_jointExpectedResetIncrement_continuous _ _ (twoWeights_sum p)
      hvanish (twoShifts_vanish hlam) hcont (twoShifts_continuous (dd : ℝ)))
    lam (ageCounter_totalIntensity_le _ _ (twoWeights_sum p) (rampRate_le hlam.le _))
    (L1 * 1 + L2) (by nlinarith)
    (ageCounter_jointExpectedResetIncrement_lipschitz _ _ (twoWeights_sum p)
      hvanish (twoShifts_vanish hlam) hL1' hL1 hL2 (twoShifts_lipschitz (dd : ℝ)))
    dd hdd (le_twoChannelNoise_holdingTime lam dd)
    (ageCounter_jointFlowIntegralIdentity _ _ hderiv hc')

/-- **The Dynkin identity for the amplitude-modulated cosine** on the
two-channel refractory clock: a non-separable test function of the age and the
counter. -/
theorem twoChannel_dynkin_rampCos (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (ageCounterJointTest (rampCosProfileDeriv (dd : ℝ)))
      (ageCounterJointTest (rampCosProfile (dd : ℝ))) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 :=
  twoChannel_dynkin_jointProfile hlam hdd hp0 hp1
    (measurable_rampCosProfile (dd : ℝ)) (continuous_rampCosProfile (dd : ℝ))
    (abs_rampCosProfile_le (dd : ℝ)) zero_le_one
    (rampCosProfile_lipschitz_counter dd.coe_nonneg) zero_le_one
    (rampCosProfile_lipschitz_age (dd : ℝ))
    (fun a ha => rampCosProfile_flat dd.coe_nonneg a ha)
    (hasDerivAt_rampCosProfile (dd : ℝ)) (continuous_rampCosProfileDeriv (dd : ℝ)) t₀ t

/-- **The martingale property for the amplitude-modulated cosine** on the
two-channel refractory clock. -/
theorem twoChannel_martingale_rampCos (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (ageCounterJointTest (rampCosProfileDeriv (dd : ℝ)))
        (ageCounterJointTest (rampCosProfile (dd : ℝ))))
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) :=
  twoChannel_martingale_jointProfile hlam hdd hp0 hp1
    (measurable_rampCosProfile (dd : ℝ)) (continuous_rampCosProfile (dd : ℝ))
    (abs_rampCosProfile_le (dd : ℝ)) zero_le_one
    (rampCosProfile_lipschitz_counter dd.coe_nonneg) zero_le_one
    (rampCosProfile_lipschitz_age (dd : ℝ))
    (fun a ha => rampCosProfile_flat dd.coe_nonneg a ha)
    (hasDerivAt_rampCosProfile (dd : ℝ)) (continuous_rampCosProfileDeriv (dd : ℝ)) t₀

end TwoChannelJoint

end SHS
