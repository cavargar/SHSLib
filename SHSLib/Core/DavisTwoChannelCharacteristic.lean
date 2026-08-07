import SHSLib.Core.DavisTwoChannelClock

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # The characteristic family on the two-channel refractory clock

The two-channel refractory clock of `SHSLib.Core.DavisTwoChannelClock` carries
the Dynkin identity and the martingale property for *every* bounded Lipschitz
profile of the counter (`twoChannel_dynkin_of_profile` and
`twoChannel_martingale_of_profile`).  This module instantiates that family at
the trigonometric profiles

* `fun c => Real.cos (theta * c)` and
* `fun c => Real.sin (theta * c)`,

for an arbitrary frequency `theta : ℝ`.  Each of them is bounded by one and
Lipschitz with constant `|theta|`, so both conclusions hold with no hypotheses
beyond `0 < lam`, `0 < dd` and `0 ≤ p ≤ 1`.

Together the two profiles are the real and imaginary parts of the characteristic
function `c ↦ exp (I · theta · c)` of the counter, so the pair of statements is
exactly the assertion that the occupation-compensated characteristic function of
the counter has zero mean and is a martingale at every frequency.  Since a
finite measure on `ℝ` is determined by its characteristic function, the family
indexed by `theta` separates the laws of the counter, which is the reason for
recording the whole family rather than a single test function.
-/

namespace SHS

namespace TwoChannelCharacteristic

/-! ## The trigonometric profiles -/

/-- The cosine profile at frequency `theta`. -/
def cosProfile (theta : ℝ) : ℝ → ℝ := fun c => Real.cos (theta * c)

/-- The sine profile at frequency `theta`. -/
def sinProfile (theta : ℝ) : ℝ → ℝ := fun c => Real.sin (theta * c)

theorem continuous_cosProfile (theta : ℝ) : Continuous (cosProfile theta) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_id)

theorem continuous_sinProfile (theta : ℝ) : Continuous (sinProfile theta) :=
  Real.continuous_sin.comp (continuous_const.mul continuous_id)

theorem measurable_cosProfile (theta : ℝ) : Measurable (cosProfile theta) :=
  (continuous_cosProfile theta).measurable

theorem measurable_sinProfile (theta : ℝ) : Measurable (sinProfile theta) :=
  (continuous_sinProfile theta).measurable

theorem abs_cosProfile_le (theta : ℝ) (c : ℝ) : |cosProfile theta c| ≤ 1 :=
  Real.abs_cos_le_one _

theorem abs_sinProfile_le (theta : ℝ) (c : ℝ) : |sinProfile theta c| ≤ 1 :=
  Real.abs_sin_le_one _

theorem cosProfile_lipschitz (theta : ℝ) (y y' : ℝ) :
    |cosProfile theta y - cosProfile theta y'| ≤ |theta| * |y - y'| := by
  have h := Real.lipschitzWith_cos.dist_le_mul (theta * y) (theta * y')
  rw [Real.dist_eq, Real.dist_eq] at h
  calc |cosProfile theta y - cosProfile theta y'| ≤ |theta * y - theta * y'| := by
        simpa [cosProfile] using h
    _ = |theta| * |y - y'| := by rw [← mul_sub, abs_mul]

theorem sinProfile_lipschitz (theta : ℝ) (y y' : ℝ) :
    |sinProfile theta y - sinProfile theta y'| ≤ |theta| * |y - y'| := by
  have h := Real.lipschitzWith_sin.dist_le_mul (theta * y) (theta * y')
  rw [Real.dist_eq, Real.dist_eq] at h
  calc |sinProfile theta y - sinProfile theta y'| ≤ |theta * y - theta * y'| := by
        simpa [sinProfile] using h
    _ = |theta| * |y - y'| := by rw [← mul_sub, abs_mul]

end TwoChannelCharacteristic

open TwoChannelCharacteristic

section Characteristic

variable {lam : ℝ} (hlam : 0 < lam) {dd : ℝ≥0} (hdd : 0 < dd) {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1)

include hlam hdd hp0 hp1

/-- **The Dynkin identity at the cosine of the counter at frequency `theta`.** -/
theorem twoChannel_dynkin_cosProfile (theta : ℝ) (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (fun _ => 0) (counterTestFunction (cosProfile theta)) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 :=
  twoChannel_dynkin_of_profile hlam hdd hp0 hp1 (measurable_cosProfile theta)
    (continuous_cosProfile theta) (abs_cosProfile_le theta) (abs_nonneg theta)
    (cosProfile_lipschitz theta) t₀ t

/-- **The Dynkin identity at the sine of the counter at frequency `theta`.** -/
theorem twoChannel_dynkin_sinProfile (theta : ℝ) (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (fun _ => 0) (counterTestFunction (sinProfile theta)) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 :=
  twoChannel_dynkin_of_profile hlam hdd hp0 hp1 (measurable_sinProfile theta)
    (continuous_sinProfile theta) (abs_sinProfile_le theta) (abs_nonneg theta)
    (sinProfile_lipschitz theta) t₀ t

/-- **The martingale property at the cosine of the counter at frequency
`theta`.** -/
theorem twoChannel_martingale_cosProfile (theta : ℝ) (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (fun _ => 0) (counterTestFunction (cosProfile theta)))
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) :=
  twoChannel_martingale_of_profile hlam hdd hp0 hp1 (measurable_cosProfile theta)
    (continuous_cosProfile theta) (abs_cosProfile_le theta) (abs_nonneg theta)
    (cosProfile_lipschitz theta) t₀

/-- **The martingale property at the sine of the counter at frequency
`theta`.** -/
theorem twoChannel_martingale_sinProfile (theta : ℝ) (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (fun _ => 0) (counterTestFunction (sinProfile theta)))
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) :=
  twoChannel_martingale_of_profile hlam hdd hp0 hp1 (measurable_sinProfile theta)
    (continuous_sinProfile theta) (abs_sinProfile_le theta) (abs_nonneg theta)
    (sinProfile_lipschitz theta) t₀

/-- **The Dynkin identity for the characteristic function of the counter**: the
real and the imaginary part of `c ↦ exp (I · theta · c)` both have
occupation-compensated increments of zero mean, at every frequency `theta` and
every elapsed time. -/
theorem twoChannel_dynkin_characteristic (theta : ℝ) (t₀ : ℝ) (t : ℝ≥0) :
    (∫ om, davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
        (fun _ => 0) (counterTestFunction (cosProfile theta)) t om
        ∂(twoChannelMeasure p hp0 hp1) = 0) ∧
      ∫ om, davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
        (fun _ => 0) (counterTestFunction (sinProfile theta)) t om
        ∂(twoChannelMeasure p hp0 hp1) = 0 :=
  ⟨twoChannel_dynkin_cosProfile hlam hdd hp0 hp1 theta t₀ t,
    twoChannel_dynkin_sinProfile hlam hdd hp0 hp1 theta t₀ t⟩

end Characteristic

end SHS
