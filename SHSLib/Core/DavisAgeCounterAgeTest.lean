import SHSLib.Core.DavisAgeCounterModel
import SHSLib.Core.DavisAgeClockTestFunction

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Test functions of the age on the multi-channel age–counter clock

The test functions used so far on the age–counter clock of
`SHSLib.Core.DavisAgeCounterModel` are functions of the *counter*, which is
constant along the flow; their flow generator therefore vanishes and the flow
integral identity is trivial.  This module treats the complementary case: test
functions of the *age*,

`g z = hfun (age z)`,

whose flow generator is genuinely nonzero, because the age grows at unit speed.

All the channels of the model send the age back to zero, so a reset always
carries the test function to `hfun 0`, whatever the channel; the expected reset
increment is therefore the same expression `hfun 0 − hfun (age)` as for a
one-channel age clock, provided `hfun` agrees with `hfun 0` wherever the rate
vanishes (there the normalized channel weights are undefined, and the increment
must vanish for continuity).  The occupation density is
`(hfun 0 − hfun (age)) · rate (age)`, the same one-dimensional profile
`ageOccupationDensity` as for the age clock, so the results of
`SHSLib.Core.DavisAgeClockTestFunction` about that profile are reused verbatim.

The new content is the **flow integral identity**: with `hfun` differentiable
with continuous derivative `hfun'`, the fundamental theorem of calculus gives

`g (flow u z) − g z = ∫_0^u hfun' (age z + s) ds`,

i.e. the flow generator is `z ↦ hfun' (age z)`.
-/

namespace SHS

section AgeTest

variable {m : ℕ} {rate : ℝ → ℝ} {w : Fin m → ℝ} {shift : Fin m → ℝ → ℝ}
  {hfun hfun' : ℝ → ℝ} (hrate : ∀ y, 0 ≤ rate y) (hw : ∀ l, 0 ≤ w l)

/-- A test function of the age alone, on the two-coordinate state of the
age–counter clock. -/
def ageCounterAgeTest (hfun : ℝ → ℝ) : DavisState Bool 2 → ℝ := fun z => hfun (z.2.1 0)

theorem measurable_ageCounterAgeTest (hm : Measurable hfun) :
    Measurable (ageCounterAgeTest hfun) := by
  have hage : Measurable fun z : DavisState Bool 2 => z.2.1 0 := by fun_prop
  exact hm.comp hage

theorem abs_ageCounterAgeTest_le {C : ℝ} (hC : ∀ y, |hfun y| ≤ C)
    (z : DavisState Bool 2) : |ageCounterAgeTest hfun z| ≤ C := hC _

/-- Every channel zeroes the age, so a reset always carries an age test function
to its value at age zero. -/
@[simp] theorem ageCounterAgeTest_reset (l : Fin m) (z : DavisState Bool 2) :
    ageCounterAgeTest hfun
        ((ageCounterSHS rate w shift hrate hw).resetDavisState l z) = hfun 0 := by
  show hfun (((ageCounterSHS rate w shift hrate hw).resetDavisState l z).2.1 0) = hfun 0
  rw [ageCounter_reset_age]

/-! ## The expected reset increment -/

/-- **The expected reset increment of an age test function** does not see the
channels: they all zero the age. -/
theorem ageCounter_ageExpectedResetIncrement (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0) (z : DavisState Bool 2) :
    davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (ageCounterAgeTest hfun) z = hfun 0 - hfun (z.2.1 0) := by
  rw [davisExpectedResetIncrement]
  have hterm : ∀ l : Fin m,
      davisChannelProbability (ageCounterSHS rate w shift hrate hw) z l *
          (ageCounterAgeTest hfun
              ((ageCounterSHS rate w shift hrate hw).resetDavisState l z) -
            ageCounterAgeTest hfun z)
        = w l * (hfun 0 - hfun (z.2.1 0)) := by
    intro l
    have hprob : davisChannelProbability (ageCounterSHS rate w shift hrate hw) z l
        = w l * rate (z.2.1 0) / rate (z.2.1 0) := by
      rw [davisChannelProbability, ageCounter_totalIntensity hrate hw hw1]
      rfl
    rw [ageCounterAgeTest_reset hrate hw l z, hprob]
    show w l * rate (z.2.1 0) / rate (z.2.1 0) * (hfun 0 - hfun (z.2.1 0))
      = w l * (hfun 0 - hfun (z.2.1 0))
    by_cases h0 : rate (z.2.1 0) = 0
    · rw [h0, mul_zero, zero_div, zero_mul, hvanish _ h0, sub_self, mul_zero]
    · rw [mul_div_assoc, div_self h0, mul_one]
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.sum_mul, hw1, one_mul]

/-- Continuity of the expected reset increment along the flow. -/
theorem ageCounter_ageExpectedResetIncrement_continuous (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0) (hf : Continuous hfun)
    (z : DavisState Bool 2) :
    Continuous fun s : ℝ => davisExpectedResetIncrement
      (ageCounterSHS rate w shift hrate hw) (ageCounterAgeTest hfun)
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z) := by
  have hrw : (fun s : ℝ => davisExpectedResetIncrement
      (ageCounterSHS rate w shift hrate hw) (ageCounterAgeTest hfun)
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z))
      = fun s : ℝ => hfun 0 - hfun (z.2.1 0 + max s 0) := by
    funext s
    simp only [ageCounter_ageExpectedResetIncrement hrate hw hw1 hvanish,
      ageCounter_davisFlow_age, Real.coe_toNNReal']
  rw [hrw]
  exact continuous_const.sub (hf.comp (continuous_const.add
    (continuous_id.max continuous_const)))

/-- A Lipschitz profile of the age gives a Lipschitz expected reset increment
along the flow. -/
theorem ageCounter_ageExpectedResetIncrement_lipschitz (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0) {L : ℝ}
    (hL : ∀ y y' : ℝ, |hfun y - hfun y'| ≤ L * |y - y'|)
    (z : DavisState Bool 2) (u v : ℝ≥0) :
    |davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (ageCounterAgeTest hfun)
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) u z) -
      davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (ageCounterAgeTest hfun)
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) v z)|
      ≤ L * |(u : ℝ) - (v : ℝ)| := by
  rw [ageCounter_ageExpectedResetIncrement hrate hw hw1 hvanish,
    ageCounter_ageExpectedResetIncrement hrate hw hw1 hvanish,
    ageCounter_davisFlow_age, ageCounter_davisFlow_age]
  have hsub : (hfun 0 - hfun (z.2.1 0 + (u : ℝ))) - (hfun 0 - hfun (z.2.1 0 + (v : ℝ)))
      = hfun (z.2.1 0 + (v : ℝ)) - hfun (z.2.1 0 + (u : ℝ)) := by ring
  rw [hsub]
  have h := hL (z.2.1 0 + (v : ℝ)) (z.2.1 0 + (u : ℝ))
  have habs : |z.2.1 0 + (v : ℝ) - (z.2.1 0 + (u : ℝ))| = |(u : ℝ) - (v : ℝ)| := by
    rw [show z.2.1 0 + (v : ℝ) - (z.2.1 0 + (u : ℝ)) = -((u : ℝ) - (v : ℝ)) by ring,
      abs_neg]
  rwa [habs] at h

/-! ## The reset occupation -/

/-- **The reset occupation density of an age test function** is the same
one-dimensional profile as for a one-channel age clock. -/
theorem ageCounter_ageResetOccupationDensity (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0) (z : DavisState Bool 2) (s : ℝ) :
    davisSegmentResetOccupationDensity (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) (ageCounterAgeTest hfun) z s
      = ageOccupationDensity rate hfun (z.2.1 0 + max s 0) := by
  rw [davisSegmentResetOccupationDensity,
    ageCounter_ageExpectedResetIncrement hrate hw hw1 hvanish,
    ageCounter_totalIntensity hrate hw hw1, ageCounter_davisFlow_age,
    Real.coe_toNNReal']
  rw [ageOccupationDensity]
  ring

/-- Continuity of the reset occupation density along the flow. -/
theorem ageCounter_ageResetOccupationContinuousAlongFlow (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0) (hc : Continuous rate)
    (hf : Continuous hfun) :
    DavisResetOccupationContinuousAlongFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterAgeTest hfun) := by
  intro z
  have hrw : davisSegmentResetOccupationDensity (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterAgeTest hfun) z
      = fun s : ℝ => ageOccupationDensity rate hfun (z.2.1 0 + max s 0) :=
    funext fun s => ageCounter_ageResetOccupationDensity hrate hw hw1 hvanish z s
  rw [hrw]
  exact (continuous_ageOccupationDensity hc hf).comp
    (continuous_const.add (continuous_id.max continuous_const))

/-- **Regularity of the reset occupation** of an age test function, through the
criterion of `SHSLib.Core.DavisOccupationRegularCriterion`. -/
theorem ageCounter_ageResetOccupationRegular (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0) (hrm : Measurable rate)
    (hc : Continuous rate) (hfm : Measurable hfun) (hf : Continuous hfun)
    (hsm : ∀ l, Measurable (shift l)) :
    DavisResetOccupationRegular (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterAgeTest hfun) := by
  haveI := ageCounter_intensitiesMeasurable (shift := shift) hrate hw hrm
  exact davisResetOccupationRegular_of_measurable _
    (ageCounter_flowRegular hrate hw) (ageCounter_resetRegular hrate hw hsm)
    (measurable_ageCounterAgeTest hfm)
    (ageCounter_ageResetOccupationContinuousAlongFlow hrate hw hw1 hvanish hc hf)

/-! ## The flow integral identity -/

/-- **The flow integral identity for an age test function**, with the derivative
of the one-dimensional profile as flow generator.  Unlike for a test function of
the counter, the flow generator is genuinely nonzero. -/
theorem ageCounter_ageFlowIntegralIdentity
    (hderiv : ∀ y, HasDerivAt hfun (hfun' y) y) (hc : Continuous hfun') :
    DavisFlowIntegralIdentity (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterAgeTest hfun)
      (ageCounterAgeTest hfun') := by
  intro z u
  have hcongr : Set.EqOn
      (fun s : ℝ => ageCounterAgeTest hfun'
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) s.toNNReal z))
      (fun s : ℝ => hfun' (z.2.1 0 + s)) (Set.Icc (0 : ℝ) (u : ℝ)) := by
    intro s hs
    show hfun' ((davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) s.toNNReal z).2.1 0) = _
    rw [ageCounter_davisFlow_age, Real.coe_toNNReal _ hs.1]
  rw [davisFlowDensityIntegral, setIntegral_congr_fun measurableSet_Icc hcongr,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le u.coe_nonneg,
    intervalIntegral.integral_comp_add_left hfun' (z.2.1 0), add_zero,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hc.intervalIntegrable _ _)]
  show hfun ((davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) u z).2.1 0) - hfun (z.2.1 0) = _
  rw [ageCounter_davisFlow_age]

end AgeTest

end SHS
