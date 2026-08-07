import SHSLib.Core.DavisAgeCounterAgeTest

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Test functions of the age and the counter together

The age–counter clock of `SHSLib.Core.DavisAgeCounterModel` now carries two
separate hypothesis packages: one for test functions of the counter alone, whose
flow generator vanishes, and one for test functions of the age alone
(`SHSLib.Core.DavisAgeCounterAgeTest`), whose expected reset increment does not
see the channels.  This module combines them, for the *additively separable*
test functions

`g z = f (age z) + k (counter z)`.

The combination is cheap because the expected reset increment is linear in the
test function: `davisExpectedResetIncrement_add` below, which holds for any
Davis model whatsoever.  Consequently the increment of a mixed test function is
the sum of the two increments already computed, its occupation density is the
sum of the two densities, and continuity, the Lipschitz bound and regularity all
follow from the corresponding results for the two summands.  The flow integral
identity is the one of the age part alone, since the counter does not move along
the flow.

The mixed test functions are the first ones on this family for which both parts
of the Davis generator are present at once: the flow part comes from `f`, the
channel-dependent part of the jump term from `k`.
-/

namespace SHS

/-! ## Linearity of the one-reset expectation -/

section Linearity

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q] {n m : ℕ}

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- **The expected reset increment is additive in the test function.** -/
theorem davisExpectedResetIncrement_add (S : SHS Q n m)
    (g1 g2 : DavisState Q n → ℝ) (z : DavisState Q n) :
    davisExpectedResetIncrement S (fun x => g1 x + g2 x) z
      = davisExpectedResetIncrement S g1 z + davisExpectedResetIncrement S g2 z := by
  rw [davisExpectedResetIncrement, davisExpectedResetIncrement,
    davisExpectedResetIncrement, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The reset occupation density is additive in the test function. -/
theorem davisSegmentResetOccupationDensity_add (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) (g1 g2 : DavisState Q n → ℝ) (z : DavisState Q n)
    (s : ℝ) :
    davisSegmentResetOccupationDensity S hflow (fun x => g1 x + g2 x) z s
      = davisSegmentResetOccupationDensity S hflow g1 z s +
        davisSegmentResetOccupationDensity S hflow g2 z s := by
  rw [davisSegmentResetOccupationDensity, davisSegmentResetOccupationDensity,
    davisSegmentResetOccupationDensity, davisExpectedResetIncrement_add]
  ring

end Linearity

/-! ## The mixed test function -/

section MixedTest

variable {m : ℕ} {rate : ℝ → ℝ} {w : Fin m → ℝ} {shift : Fin m → ℝ → ℝ}
  {f k : ℝ → ℝ} (hrate : ∀ y, 0 ≤ rate y) (hw : ∀ l, 0 ≤ w l)

/-- An additively separable test function of the age and the counter. -/
def ageCounterMixedTest (f k : ℝ → ℝ) : DavisState Bool 2 → ℝ :=
  fun z => ageCounterAgeTest f z + counterTestFunction k z

theorem measurable_ageCounterMixedTest (hfm : Measurable f) (hkm : Measurable k) :
    Measurable (ageCounterMixedTest f k) :=
  (measurable_ageCounterAgeTest hfm).add (measurable_counterTestFunction hkm)

theorem abs_ageCounterMixedTest_le {Cf Ck : ℝ} (hf : ∀ y, |f y| ≤ Cf)
    (hk : ∀ y, |k y| ≤ Ck) (z : DavisState Bool 2) :
    |ageCounterMixedTest f k z| ≤ Cf + Ck :=
  (abs_add_le _ _).trans (add_le_add (hf _) (hk _))

/-- **The expected reset increment of a mixed test function** is the sum of the
two increments: the age part does not see the channels, the counter part mixes
them. -/
theorem ageCounter_mixedExpectedResetIncrement (hw1 : ∑ l, w l = 1)
    (hfvanish : ∀ y, rate y = 0 → f y = f 0)
    (hsvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) (z : DavisState Bool 2) :
    davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (ageCounterMixedTest f k) z
      = (f 0 - f (z.2.1 0)) +
        ∑ l, w l * (k (z.2.1 1 + shift l (z.2.1 0)) - k (z.2.1 1)) := by
  have hdef : ageCounterMixedTest f k
      = fun x => ageCounterAgeTest f x + counterTestFunction k x := rfl
  rw [hdef, davisExpectedResetIncrement_add,
    ageCounter_ageExpectedResetIncrement hrate hw hw1 hfvanish,
    ageCounter_expectedResetIncrement hrate hw hw1 hsvanish]

/-- Continuity of the expected reset increment of a mixed test function along
the flow. -/
theorem ageCounter_mixedExpectedResetIncrement_continuous (hw1 : ∑ l, w l = 1)
    (hfvanish : ∀ y, rate y = 0 → f y = f 0)
    (hsvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) (hfc : Continuous f)
    (hkc : Continuous k) (hs : ∀ l, Continuous (shift l)) (z : DavisState Bool 2) :
    Continuous fun s : ℝ => davisExpectedResetIncrement
      (ageCounterSHS rate w shift hrate hw) (ageCounterMixedTest f k)
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z) := by
  have hrw : (fun s : ℝ => davisExpectedResetIncrement
      (ageCounterSHS rate w shift hrate hw) (ageCounterMixedTest f k)
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z))
      = (fun s : ℝ => davisExpectedResetIncrement
          (ageCounterSHS rate w shift hrate hw) (ageCounterAgeTest f)
          (davisFlow (ageCounterSHS rate w shift hrate hw)
            (ageCounterFlow rate w shift hrate hw) s.toNNReal z)) +
        fun s : ℝ => davisExpectedResetIncrement
          (ageCounterSHS rate w shift hrate hw) (counterTestFunction k)
          (davisFlow (ageCounterSHS rate w shift hrate hw)
            (ageCounterFlow rate w shift hrate hw) s.toNNReal z) := by
    funext s
    exact davisExpectedResetIncrement_add _ _ _ _
  rw [hrw]
  exact (ageCounter_ageExpectedResetIncrement_continuous hrate hw hw1 hfvanish hfc z).add
    (ageCounter_expectedResetIncrement_continuous hrate hw hw1 hsvanish hkc hs z)

/-- The Lipschitz bound of a mixed test function along the flow: the two
constants add. -/
theorem ageCounter_mixedExpectedResetIncrement_lipschitz (hw1 : ∑ l, w l = 1)
    (hfvanish : ∀ y, rate y = 0 → f y = f 0)
    (hsvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) {Lf Lk Ls : ℝ}
    (hfL : ∀ y y' : ℝ, |f y - f y'| ≤ Lf * |y - y'|) (hLk : 0 ≤ Lk)
    (hkL : ∀ y y' : ℝ, |k y - k y'| ≤ Lk * |y - y'|)
    (hsL : ∀ (l : Fin m) (y y' : ℝ), |shift l y - shift l y'| ≤ Ls * |y - y'|)
    (z : DavisState Bool 2) (u v : ℝ≥0) :
    |davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (ageCounterMixedTest f k)
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) u z) -
      davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (ageCounterMixedTest f k)
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) v z)|
      ≤ (Lf + Lk * Ls) * |(u : ℝ) - (v : ℝ)| := by
  have hdef : ageCounterMixedTest f k
      = fun x => ageCounterAgeTest f x + counterTestFunction k x := rfl
  rw [hdef, davisExpectedResetIncrement_add, davisExpectedResetIncrement_add]
  have hage := ageCounter_ageExpectedResetIncrement_lipschitz (shift := shift) hrate hw
    hw1 hfvanish hfL z u v
  have hcounter := ageCounter_expectedResetIncrement_lipschitz hrate hw hw1 hsvanish
    hLk hkL hsL z u v
  have hsplit :
      (davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
          (ageCounterAgeTest f)
          (davisFlow (ageCounterSHS rate w shift hrate hw)
            (ageCounterFlow rate w shift hrate hw) u z) +
        davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
          (counterTestFunction k)
          (davisFlow (ageCounterSHS rate w shift hrate hw)
            (ageCounterFlow rate w shift hrate hw) u z)) -
      (davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
          (ageCounterAgeTest f)
          (davisFlow (ageCounterSHS rate w shift hrate hw)
            (ageCounterFlow rate w shift hrate hw) v z) +
        davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
          (counterTestFunction k)
          (davisFlow (ageCounterSHS rate w shift hrate hw)
            (ageCounterFlow rate w shift hrate hw) v z))
      = (davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
            (ageCounterAgeTest f)
            (davisFlow (ageCounterSHS rate w shift hrate hw)
              (ageCounterFlow rate w shift hrate hw) u z) -
          davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
            (ageCounterAgeTest f)
            (davisFlow (ageCounterSHS rate w shift hrate hw)
              (ageCounterFlow rate w shift hrate hw) v z)) +
        (davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
            (counterTestFunction k)
            (davisFlow (ageCounterSHS rate w shift hrate hw)
              (ageCounterFlow rate w shift hrate hw) u z) -
          davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
            (counterTestFunction k)
            (davisFlow (ageCounterSHS rate w shift hrate hw)
              (ageCounterFlow rate w shift hrate hw) v z)) := by ring
  rw [hsplit, add_mul]
  exact (abs_add_le _ _).trans (add_le_add hage hcounter)

/-- Continuity of the reset occupation density of a mixed test function along
the flow. -/
theorem ageCounter_mixedResetOccupationContinuousAlongFlow (hw1 : ∑ l, w l = 1)
    (hfvanish : ∀ y, rate y = 0 → f y = f 0)
    (hsvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) (hc : Continuous rate)
    (hfc : Continuous f) (hkc : Continuous k) (hs : ∀ l, Continuous (shift l)) :
    DavisResetOccupationContinuousAlongFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterMixedTest f k) := by
  intro z
  have hrw : davisSegmentResetOccupationDensity (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterMixedTest f k) z
      = (fun s : ℝ => davisSegmentResetOccupationDensity
          (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) (ageCounterAgeTest f) z s) +
        fun s : ℝ => davisSegmentResetOccupationDensity
          (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) (counterTestFunction k) z s := by
    funext s
    exact davisSegmentResetOccupationDensity_add _ _ _ _ _ _
  rw [hrw]
  exact (ageCounter_ageResetOccupationContinuousAlongFlow hrate hw hw1 hfvanish hc
    hfc z).add
    (ageCounter_resetOccupationContinuousAlongFlow hrate hw hw1 hsvanish hc hkc hs z)

/-- **Regularity of the reset occupation** of a mixed test function. -/
theorem ageCounter_mixedResetOccupationRegular (hw1 : ∑ l, w l = 1)
    (hfvanish : ∀ y, rate y = 0 → f y = f 0)
    (hsvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) (hrm : Measurable rate)
    (hc : Continuous rate) (hfm : Measurable f) (hfc : Continuous f)
    (hkm : Measurable k) (hkc : Continuous k) (hsm : ∀ l, Measurable (shift l))
    (hs : ∀ l, Continuous (shift l)) :
    DavisResetOccupationRegular (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterMixedTest f k) := by
  haveI := ageCounter_intensitiesMeasurable (shift := shift) hrate hw hrm
  exact davisResetOccupationRegular_of_measurable _
    (ageCounter_flowRegular hrate hw) (ageCounter_resetRegular hrate hw hsm)
    (measurable_ageCounterMixedTest hfm hkm)
    (ageCounter_mixedResetOccupationContinuousAlongFlow hrate hw hw1 hfvanish
      hsvanish hc hfc hkc hs)

/-- **The flow integral identity for a mixed test function**: only the age part
moves along the flow, so the flow generator is the derivative of the age
profile. -/
theorem ageCounter_mixedFlowIntegralIdentity {f' : ℝ → ℝ}
    (hderiv : ∀ y, HasDerivAt f (f' y) y) (hc' : Continuous f') :
    DavisFlowIntegralIdentity (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterMixedTest f k)
      (ageCounterAgeTest f') := by
  intro z u
  have hage := ageCounter_ageFlowIntegralIdentity (shift := shift) hrate hw hderiv hc' z u
  have hcounter : counterTestFunction k
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) u z)
      = counterTestFunction k z := by
    show k ((davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) u z).2.1 1) = k (z.2.1 1)
    rw [ageCounter_davisFlow_counter]
  show (ageCounterAgeTest f (davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) u z) +
      counterTestFunction k (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) u z)) -
      (ageCounterAgeTest f z + counterTestFunction k z) = _
  rw [hcounter]
  rw [show ∀ a b c : ℝ, a + c - (b + c) = a - b from fun a b c => by ring]
  exact hage

end MixedTest

end SHS
