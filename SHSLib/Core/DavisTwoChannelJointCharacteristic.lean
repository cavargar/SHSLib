import SHSLib.Core.DavisTwoChannelJointTest

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # The joint characteristic family on the two-channel refractory clock

`SHSLib.Core.DavisTwoChannelCharacteristic` records the Dynkin identity and the
martingale property at the trigonometric profiles of the *counter* alone, a
family which separates the laws of the counter but says nothing about its joint
law with the age.  With the joint test-function theory in place
(`SHSLib.Core.DavisTwoChannelJointTest`) that restriction can be lifted.

The profiles of this module are the real and imaginary parts of

`exp (I · (theta · flatRamp dd (age) + nu · counter))`,

for arbitrary frequencies `theta` and `nu`.  The age enters through the flat
ramp rather than directly: a test function of this clock must not depend on the
age below the dead time, where the rate vanishes, and the flat ramp is the
canonical way to build that constraint into the age argument.  The family is
therefore the characteristic family of the *pair*

`(flatRamp dd (age), counter)`,

and separates the joint laws of that pair, not merely the two marginals.

Both profiles are bounded by one, Lipschitz in the counter with constant `|nu|`
and Lipschitz in the age with constant `|theta|`, so — as for every family on
this clock — the two conclusions need no hypotheses beyond `0 < lam`, `0 < dd`
and `0 ≤ p ≤ 1`.
-/

namespace SHS

namespace TwoChannelJointCharacteristic

/-! ## The joint phase and the two trigonometric profiles -/

/-- The phase `theta · flatRamp d a + nu · c`, a function of the age `a` and the
counter `c` which is constant in the age below the dead time `d`. -/
def jointPhase (d theta nu : ℝ) : ℝ → ℝ → ℝ := fun a c => theta * flatRamp d a + nu * c

/-- The derivative of the phase in the age. -/
def jointPhaseDeriv (d theta : ℝ) : ℝ → ℝ := fun a => theta * flatRampDeriv d a

/-- The joint cosine profile at frequencies `theta` (age) and `nu` (counter). -/
def jointCosProfile (d theta nu : ℝ) : ℝ → ℝ → ℝ :=
  fun a c => Real.cos (jointPhase d theta nu a c)

/-- The joint sine profile at frequencies `theta` (age) and `nu` (counter). -/
def jointSinProfile (d theta nu : ℝ) : ℝ → ℝ → ℝ :=
  fun a c => Real.sin (jointPhase d theta nu a c)

/-- The partial derivative of the joint cosine profile in the age. -/
def jointCosProfileDeriv (d theta nu : ℝ) : ℝ → ℝ → ℝ :=
  fun a c => -Real.sin (jointPhase d theta nu a c) * jointPhaseDeriv d theta a

/-- The partial derivative of the joint sine profile in the age. -/
def jointSinProfileDeriv (d theta nu : ℝ) : ℝ → ℝ → ℝ :=
  fun a c => Real.cos (jointPhase d theta nu a c) * jointPhaseDeriv d theta a

theorem continuous_jointPhase (d theta nu : ℝ) :
    Continuous (Function.uncurry (jointPhase d theta nu)) :=
  (continuous_const.mul ((continuous_flatRamp d).comp continuous_fst)).add
    (continuous_const.mul continuous_snd)

theorem continuous_jointPhaseDeriv (d theta : ℝ) : Continuous (jointPhaseDeriv d theta) :=
  continuous_const.mul (continuous_flatRampDeriv d)

theorem continuous_jointCosProfile (d theta nu : ℝ) :
    Continuous (Function.uncurry (jointCosProfile d theta nu)) :=
  Real.continuous_cos.comp (continuous_jointPhase d theta nu)

theorem continuous_jointSinProfile (d theta nu : ℝ) :
    Continuous (Function.uncurry (jointSinProfile d theta nu)) :=
  Real.continuous_sin.comp (continuous_jointPhase d theta nu)

theorem measurable_jointCosProfile (d theta nu : ℝ) :
    Measurable (Function.uncurry (jointCosProfile d theta nu)) :=
  (continuous_jointCosProfile d theta nu).measurable

theorem measurable_jointSinProfile (d theta nu : ℝ) :
    Measurable (Function.uncurry (jointSinProfile d theta nu)) :=
  (continuous_jointSinProfile d theta nu).measurable

theorem continuous_jointCosProfileDeriv (d theta nu : ℝ) :
    Continuous (Function.uncurry (jointCosProfileDeriv d theta nu)) :=
  ((Real.continuous_sin.comp (continuous_jointPhase d theta nu)).neg).mul
    ((continuous_jointPhaseDeriv d theta).comp continuous_fst)

theorem continuous_jointSinProfileDeriv (d theta nu : ℝ) :
    Continuous (Function.uncurry (jointSinProfileDeriv d theta nu)) :=
  (Real.continuous_cos.comp (continuous_jointPhase d theta nu)).mul
    ((continuous_jointPhaseDeriv d theta).comp continuous_fst)

theorem abs_jointCosProfile_le (d theta nu : ℝ) (a c : ℝ) :
    |jointCosProfile d theta nu a c| ≤ 1 := Real.abs_cos_le_one _

theorem abs_jointSinProfile_le (d theta nu : ℝ) (a c : ℝ) :
    |jointSinProfile d theta nu a c| ≤ 1 := Real.abs_sin_le_one _

/-! ## The Lipschitz bounds -/

theorem abs_cos_sub_cos_le (x y : ℝ) : |Real.cos x - Real.cos y| ≤ |x - y| := by
  have h := Real.lipschitzWith_cos.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at h
  simpa using h

theorem abs_sin_sub_sin_le (x y : ℝ) : |Real.sin x - Real.sin y| ≤ |x - y| := by
  have h := Real.lipschitzWith_sin.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq] at h
  simpa using h

theorem jointPhase_sub_counter (d theta nu a c c' : ℝ) :
    jointPhase d theta nu a c - jointPhase d theta nu a c' = nu * (c - c') := by
  simp only [jointPhase]
  ring

theorem jointPhase_sub_age (d theta nu a a' c : ℝ) :
    jointPhase d theta nu a c - jointPhase d theta nu a' c
      = theta * (flatRamp d a - flatRamp d a') := by
  simp only [jointPhase]
  ring

theorem jointCosProfile_lipschitz_counter (d theta nu c c' : ℝ) :
    |jointCosProfile d theta nu 0 c - jointCosProfile d theta nu 0 c'| ≤ |nu| * |c - c'| := by
  calc |jointCosProfile d theta nu 0 c - jointCosProfile d theta nu 0 c'|
      ≤ |jointPhase d theta nu 0 c - jointPhase d theta nu 0 c'| := abs_cos_sub_cos_le _ _
    _ = |nu| * |c - c'| := by rw [jointPhase_sub_counter, abs_mul]

theorem jointSinProfile_lipschitz_counter (d theta nu c c' : ℝ) :
    |jointSinProfile d theta nu 0 c - jointSinProfile d theta nu 0 c'| ≤ |nu| * |c - c'| := by
  calc |jointSinProfile d theta nu 0 c - jointSinProfile d theta nu 0 c'|
      ≤ |jointPhase d theta nu 0 c - jointPhase d theta nu 0 c'| := abs_sin_sub_sin_le _ _
    _ = |nu| * |c - c'| := by rw [jointPhase_sub_counter, abs_mul]

theorem abs_jointPhase_sub_age_le (d theta nu a a' c : ℝ) :
    |jointPhase d theta nu a c - jointPhase d theta nu a' c| ≤ |theta| * |a - a'| := by
  rw [jointPhase_sub_age, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg theta)
  simpa using flatRamp_lipschitz d a a'

theorem jointCosProfile_lipschitz_age (d theta nu a a' c : ℝ) :
    |jointCosProfile d theta nu a c - jointCosProfile d theta nu a' c| ≤ |theta| * |a - a'| :=
  le_trans (abs_cos_sub_cos_le _ _) (abs_jointPhase_sub_age_le d theta nu a a' c)

theorem jointSinProfile_lipschitz_age (d theta nu a a' c : ℝ) :
    |jointSinProfile d theta nu a c - jointSinProfile d theta nu a' c| ≤ |theta| * |a - a'| :=
  le_trans (abs_sin_sub_sin_le _ _) (abs_jointPhase_sub_age_le d theta nu a a' c)

/-! ## Flatness below the dead time and the derivative in the age -/

theorem jointPhase_flat {d : ℝ} (hd : 0 ≤ d) (theta nu : ℝ) {a : ℝ} (ha : a ≤ d) (c : ℝ) :
    jointPhase d theta nu a c = jointPhase d theta nu 0 c := by
  simp only [jointPhase, flatRamp_of_le ha, flatRamp_of_le hd]

theorem jointCosProfile_flat {d : ℝ} (hd : 0 ≤ d) (theta nu : ℝ) {a : ℝ} (ha : a ≤ d) (c : ℝ) :
    jointCosProfile d theta nu a c = jointCosProfile d theta nu 0 c := by
  simp only [jointCosProfile, jointPhase_flat hd theta nu ha c]

theorem jointSinProfile_flat {d : ℝ} (hd : 0 ≤ d) (theta nu : ℝ) {a : ℝ} (ha : a ≤ d) (c : ℝ) :
    jointSinProfile d theta nu a c = jointSinProfile d theta nu 0 c := by
  simp only [jointSinProfile, jointPhase_flat hd theta nu ha c]

theorem hasDerivAt_jointPhase (d theta nu a c : ℝ) :
    HasDerivAt (fun x => jointPhase d theta nu x c) (jointPhaseDeriv d theta a) a := by
  simpa [jointPhase, jointPhaseDeriv] using
    (((hasDerivAt_flatRamp d a).const_mul theta).add_const (nu * c))

theorem hasDerivAt_jointCosProfile (d theta nu a c : ℝ) :
    HasDerivAt (fun x => jointCosProfile d theta nu x c) (jointCosProfileDeriv d theta nu a c) a := by
  simpa [jointCosProfile, jointCosProfileDeriv] using
    (Real.hasDerivAt_cos (jointPhase d theta nu a c)).comp a (hasDerivAt_jointPhase d theta nu a c)

theorem hasDerivAt_jointSinProfile (d theta nu a c : ℝ) :
    HasDerivAt (fun x => jointSinProfile d theta nu x c) (jointSinProfileDeriv d theta nu a c) a := by
  simpa [jointSinProfile, jointSinProfileDeriv] using
    (Real.hasDerivAt_sin (jointPhase d theta nu a c)).comp a (hasDerivAt_jointPhase d theta nu a c)

end TwoChannelJointCharacteristic

open TwoChannelJointCharacteristic

section JointCharacteristic

variable {lam : ℝ} (hlam : 0 < lam) {dd : ℝ≥0} (hdd : 0 < dd) {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1)

include hlam hdd hp0 hp1

/-- **The Dynkin identity at the joint cosine profile** of the flat ramp of the
age and the counter, at frequencies `theta` and `nu`. -/
theorem twoChannel_dynkin_jointCos (theta nu : ℝ) (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (ageCounterJointTest (jointCosProfileDeriv (dd : ℝ) theta nu))
      (ageCounterJointTest (jointCosProfile (dd : ℝ) theta nu)) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 :=
  twoChannel_dynkin_jointProfile hlam hdd hp0 hp1
    (measurable_jointCosProfile (dd : ℝ) theta nu)
    (continuous_jointCosProfile (dd : ℝ) theta nu)
    (abs_jointCosProfile_le (dd : ℝ) theta nu) (abs_nonneg nu)
    (jointCosProfile_lipschitz_counter (dd : ℝ) theta nu) (abs_nonneg theta)
    (jointCosProfile_lipschitz_age (dd : ℝ) theta nu)
    (fun _ ha c => jointCosProfile_flat dd.coe_nonneg theta nu ha c)
    (fun a c => hasDerivAt_jointCosProfile (dd : ℝ) theta nu a c)
    (continuous_jointCosProfileDeriv (dd : ℝ) theta nu) t₀ t

/-- **The Dynkin identity at the joint sine profile** of the flat ramp of the
age and the counter, at frequencies `theta` and `nu`. -/
theorem twoChannel_dynkin_jointSin (theta nu : ℝ) (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (ageCounterJointTest (jointSinProfileDeriv (dd : ℝ) theta nu))
      (ageCounterJointTest (jointSinProfile (dd : ℝ) theta nu)) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 :=
  twoChannel_dynkin_jointProfile hlam hdd hp0 hp1
    (measurable_jointSinProfile (dd : ℝ) theta nu)
    (continuous_jointSinProfile (dd : ℝ) theta nu)
    (abs_jointSinProfile_le (dd : ℝ) theta nu) (abs_nonneg nu)
    (jointSinProfile_lipschitz_counter (dd : ℝ) theta nu) (abs_nonneg theta)
    (jointSinProfile_lipschitz_age (dd : ℝ) theta nu)
    (fun _ ha c => jointSinProfile_flat dd.coe_nonneg theta nu ha c)
    (fun a c => hasDerivAt_jointSinProfile (dd : ℝ) theta nu a c)
    (continuous_jointSinProfileDeriv (dd : ℝ) theta nu) t₀ t

/-- **The martingale property at the joint cosine profile.** -/
theorem twoChannel_martingale_jointCos (theta nu : ℝ) (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀)
        (ageCounterJointTest (jointCosProfileDeriv (dd : ℝ) theta nu))
        (ageCounterJointTest (jointCosProfile (dd : ℝ) theta nu)))
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) :=
  twoChannel_martingale_jointProfile hlam hdd hp0 hp1
    (measurable_jointCosProfile (dd : ℝ) theta nu)
    (continuous_jointCosProfile (dd : ℝ) theta nu)
    (abs_jointCosProfile_le (dd : ℝ) theta nu) (abs_nonneg nu)
    (jointCosProfile_lipschitz_counter (dd : ℝ) theta nu) (abs_nonneg theta)
    (jointCosProfile_lipschitz_age (dd : ℝ) theta nu)
    (fun _ ha c => jointCosProfile_flat dd.coe_nonneg theta nu ha c)
    (fun a c => hasDerivAt_jointCosProfile (dd : ℝ) theta nu a c)
    (continuous_jointCosProfileDeriv (dd : ℝ) theta nu) t₀

/-- **The martingale property at the joint sine profile.** -/
theorem twoChannel_martingale_jointSin (theta nu : ℝ) (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀)
        (ageCounterJointTest (jointSinProfileDeriv (dd : ℝ) theta nu))
        (ageCounterJointTest (jointSinProfile (dd : ℝ) theta nu)))
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) :=
  twoChannel_martingale_jointProfile hlam hdd hp0 hp1
    (measurable_jointSinProfile (dd : ℝ) theta nu)
    (continuous_jointSinProfile (dd : ℝ) theta nu)
    (abs_jointSinProfile_le (dd : ℝ) theta nu) (abs_nonneg nu)
    (jointSinProfile_lipschitz_counter (dd : ℝ) theta nu) (abs_nonneg theta)
    (jointSinProfile_lipschitz_age (dd : ℝ) theta nu)
    (fun _ ha c => jointSinProfile_flat dd.coe_nonneg theta nu ha c)
    (fun a c => hasDerivAt_jointSinProfile (dd : ℝ) theta nu a c)
    (continuous_jointSinProfileDeriv (dd : ℝ) theta nu) t₀

end JointCharacteristic

end SHS
