import SHSLib.Core.DavisAgeCounterMixedTest

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Joint test functions of the age and the counter

The test functions available on the age–counter clock so far depend on one
coordinate, or on the two additively.  This module removes that restriction: a
*joint* test function

`g z = h (age z) (counter z)`

with `h : ℝ → ℝ → ℝ` arbitrary, subject only to regularity.  The separable
families are the special cases `h a c = f a`, `h a c = k c` and
`h a c = f a + k c`.

Nothing about the increment decomposes any more.  A reset through channel `l`
sends `(age, counter)` to `(0, counter + shift l (age))`, so the expected reset
increment is

`∑ l, w l · (h 0 (counter + shift l (age)) − h (age) (counter))`,

in which the two coordinates are entangled: the shift applied to the counter is
a function of the age at which the jump occurs.  The hypotheses accordingly
become two-dimensional: joint continuity and joint measurability of `h`, a
Lipschitz bound in the counter *at age zero* (the only age at which the counter
argument is perturbed), a Lipschitz bound in the age at a fixed counter, and,
for the flow integral identity, a partial derivative in the age with jointly
continuous derivative.

The compatibility condition also becomes two-dimensional: where the rate
vanishes, `h` must not depend on the age, `h a c = h 0 c`.
-/

namespace SHS

section JointTest

variable {m : ℕ} {rate : ℝ → ℝ} {w : Fin m → ℝ} {shift : Fin m → ℝ → ℝ}
  {h : ℝ → ℝ → ℝ} (hrate : ∀ y, 0 ≤ rate y) (hw : ∀ l, 0 ≤ w l)

/-- A joint test function of the age and the counter. -/
def ageCounterJointTest (h : ℝ → ℝ → ℝ) : DavisState Bool 2 → ℝ :=
  fun z => h (z.2.1 0) (z.2.1 1)

theorem measurable_ageCounterJointTest (hm : Measurable (Function.uncurry h)) :
    Measurable (ageCounterJointTest h) := by
  have hage : Measurable fun z : DavisState Bool 2 => z.2.1 0 := by fun_prop
  have hcounter : Measurable fun z : DavisState Bool 2 => z.2.1 1 := by fun_prop
  exact hm.comp (hage.prodMk hcounter)

theorem abs_ageCounterJointTest_le {C : ℝ} (hC : ∀ a c, |h a c| ≤ C)
    (z : DavisState Bool 2) : |ageCounterJointTest h z| ≤ C := hC _ _

/-! ## The expected reset increment -/

/-- **The expected reset increment of a joint test function.**  Where the rate
vanishes, `h` is assumed not to depend on the age, so the same expression is
valid everywhere. -/
theorem ageCounter_jointExpectedResetIncrement (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ a, rate a = 0 → ∀ c, h a c = h 0 c)
    (hsvanish : ∀ a, rate a = 0 → ∀ l, shift l a = 0) (z : DavisState Bool 2) :
    davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (ageCounterJointTest h) z
      = ∑ l, w l * (h 0 (z.2.1 1 + shift l (z.2.1 0)) - h (z.2.1 0) (z.2.1 1)) := by
  rw [davisExpectedResetIncrement]
  refine Finset.sum_congr rfl fun l => ?_
  intro _
  have hval : ageCounterJointTest h
      ((ageCounterSHS rate w shift hrate hw).resetDavisState l z)
      = h 0 (z.2.1 1 + shift l (z.2.1 0)) := by
    show h (((ageCounterSHS rate w shift hrate hw).resetDavisState l z).2.1 0)
      (((ageCounterSHS rate w shift hrate hw).resetDavisState l z).2.1 1) = _
    rw [ageCounter_reset_age, ageCounter_reset_counter]
  have hprob : davisChannelProbability (ageCounterSHS rate w shift hrate hw) z l
      = w l * rate (z.2.1 0) / rate (z.2.1 0) := by
    rw [davisChannelProbability, ageCounter_totalIntensity hrate hw hw1]
    rfl
  rw [hval, hprob]
  show w l * rate (z.2.1 0) / rate (z.2.1 0) *
      (h 0 (z.2.1 1 + shift l (z.2.1 0)) - h (z.2.1 0) (z.2.1 1))
    = w l * (h 0 (z.2.1 1 + shift l (z.2.1 0)) - h (z.2.1 0) (z.2.1 1))
  by_cases h0 : rate (z.2.1 0) = 0
  · rw [h0, mul_zero, zero_div, zero_mul, hsvanish _ h0 l, add_zero,
      hvanish _ h0 (z.2.1 1), sub_self, mul_zero]
  · rw [mul_div_assoc, div_self h0, mul_one]

/-- Continuity of the expected reset increment of a joint test function along
the flow. -/
theorem ageCounter_jointExpectedResetIncrement_continuous (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ a, rate a = 0 → ∀ c, h a c = h 0 c)
    (hsvanish : ∀ a, rate a = 0 → ∀ l, shift l a = 0)
    (hcont : Continuous (Function.uncurry h)) (hs : ∀ l, Continuous (shift l))
    (z : DavisState Bool 2) :
    Continuous fun s : ℝ => davisExpectedResetIncrement
      (ageCounterSHS rate w shift hrate hw) (ageCounterJointTest h)
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z) := by
  have hage : Continuous fun s : ℝ => z.2.1 0 + max s 0 :=
    continuous_const.add (continuous_id.max continuous_const)
  have hrw : (fun s : ℝ => davisExpectedResetIncrement
      (ageCounterSHS rate w shift hrate hw) (ageCounterJointTest h)
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z))
      = fun s : ℝ => ∑ l, w l * (h 0 (z.2.1 1 + shift l (z.2.1 0 + max s 0)) -
          h (z.2.1 0 + max s 0) (z.2.1 1)) := by
    funext s
    simp only [ageCounter_jointExpectedResetIncrement hrate hw hw1 hvanish hsvanish,
      ageCounter_davisFlow_age, ageCounter_davisFlow_counter, Real.coe_toNNReal']
  rw [hrw]
  refine continuous_finset_sum _ fun l _ => continuous_const.mul (Continuous.sub ?_ ?_)
  · exact hcont.comp (continuous_const.prodMk
      (continuous_const.add ((hs l).comp hage)))
  · exact hcont.comp (hage.prodMk continuous_const)

/-- The Lipschitz bound along the flow: the counter argument moves by the shift,
the age argument by the elapsed duration. -/
theorem ageCounter_jointExpectedResetIncrement_lipschitz (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ a, rate a = 0 → ∀ c, h a c = h 0 c)
    (hsvanish : ∀ a, rate a = 0 → ∀ l, shift l a = 0) {L1 L2 Ls : ℝ}
    (hL1' : 0 ≤ L1) (hL1 : ∀ c c' : ℝ, |h 0 c - h 0 c'| ≤ L1 * |c - c'|)
    (hL2 : ∀ a a' c : ℝ, |h a c - h a' c| ≤ L2 * |a - a'|)
    (hsL : ∀ (l : Fin m) (y y' : ℝ), |shift l y - shift l y'| ≤ Ls * |y - y'|)
    (z : DavisState Bool 2) (u v : ℝ≥0) :
    |davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (ageCounterJointTest h)
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) u z) -
      davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (ageCounterJointTest h)
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) v z)|
      ≤ (L1 * Ls + L2) * |(u : ℝ) - (v : ℝ)| := by
  set cc := z.2.1 1 with hcc
  set y := z.2.1 0 with hy
  rw [ageCounter_jointExpectedResetIncrement hrate hw hw1 hvanish hsvanish,
    ageCounter_jointExpectedResetIncrement hrate hw hw1 hvanish hsvanish,
    ageCounter_davisFlow_age, ageCounter_davisFlow_counter,
    ageCounter_davisFlow_age, ageCounter_davisFlow_counter]
  have hdiff : (∑ l, w l * (h 0 (cc + shift l (y + (u : ℝ))) - h (y + (u : ℝ)) cc)) -
      (∑ l, w l * (h 0 (cc + shift l (y + (v : ℝ))) - h (y + (v : ℝ)) cc))
      = ∑ l, w l * ((h 0 (cc + shift l (y + (u : ℝ))) -
          h 0 (cc + shift l (y + (v : ℝ)))) -
          (h (y + (u : ℝ)) cc - h (y + (v : ℝ)) cc)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hdiff]
  have hterm : ∀ l : Fin m, |w l * ((h 0 (cc + shift l (y + (u : ℝ))) -
      h 0 (cc + shift l (y + (v : ℝ)))) - (h (y + (u : ℝ)) cc - h (y + (v : ℝ)) cc))|
      ≤ w l * ((L1 * Ls + L2) * |(u : ℝ) - (v : ℝ)|) := by
    intro l
    rw [abs_mul, abs_of_nonneg (hw l)]
    refine mul_le_mul_of_nonneg_left ?_ (hw l)
    have h1 : |h 0 (cc + shift l (y + (u : ℝ))) - h 0 (cc + shift l (y + (v : ℝ)))|
        ≤ (L1 * Ls) * |(u : ℝ) - (v : ℝ)| := by
      have hstep := hL1 (cc + shift l (y + (u : ℝ))) (cc + shift l (y + (v : ℝ)))
      have hsame : |(cc + shift l (y + (u : ℝ))) - (cc + shift l (y + (v : ℝ)))|
          = |shift l (y + (u : ℝ)) - shift l (y + (v : ℝ))| := by
        congr 1
        ring
      have hshift : |shift l (y + (u : ℝ)) - shift l (y + (v : ℝ))|
          ≤ Ls * |(u : ℝ) - (v : ℝ)| := by
        have := hsL l (y + (u : ℝ)) (y + (v : ℝ))
        rwa [show y + (u : ℝ) - (y + (v : ℝ)) = (u : ℝ) - (v : ℝ) by ring] at this
      calc |h 0 (cc + shift l (y + (u : ℝ))) - h 0 (cc + shift l (y + (v : ℝ)))|
          ≤ L1 * |shift l (y + (u : ℝ)) - shift l (y + (v : ℝ))| := by
            rw [← hsame]; exact hstep
        _ ≤ L1 * (Ls * |(u : ℝ) - (v : ℝ)|) := mul_le_mul_of_nonneg_left hshift hL1'
        _ = (L1 * Ls) * |(u : ℝ) - (v : ℝ)| := by ring
    have h2 : |h (y + (u : ℝ)) cc - h (y + (v : ℝ)) cc| ≤ L2 * |(u : ℝ) - (v : ℝ)| := by
      have := hL2 (y + (u : ℝ)) (y + (v : ℝ)) cc
      rwa [show y + (u : ℝ) - (y + (v : ℝ)) = (u : ℝ) - (v : ℝ) by ring] at this
    calc |(h 0 (cc + shift l (y + (u : ℝ))) - h 0 (cc + shift l (y + (v : ℝ)))) -
          (h (y + (u : ℝ)) cc - h (y + (v : ℝ)) cc)|
        ≤ |h 0 (cc + shift l (y + (u : ℝ))) - h 0 (cc + shift l (y + (v : ℝ)))| +
          |h (y + (u : ℝ)) cc - h (y + (v : ℝ)) cc| := abs_sub _ _
      _ ≤ (L1 * Ls) * |(u : ℝ) - (v : ℝ)| + L2 * |(u : ℝ) - (v : ℝ)| :=
          add_le_add h1 h2
      _ = (L1 * Ls + L2) * |(u : ℝ) - (v : ℝ)| := by ring
  calc |∑ l, w l * ((h 0 (cc + shift l (y + (u : ℝ))) -
        h 0 (cc + shift l (y + (v : ℝ)))) - (h (y + (u : ℝ)) cc - h (y + (v : ℝ)) cc))|
      ≤ ∑ l, |w l * ((h 0 (cc + shift l (y + (u : ℝ))) -
          h 0 (cc + shift l (y + (v : ℝ)))) -
          (h (y + (u : ℝ)) cc - h (y + (v : ℝ)) cc))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin m, w l * ((L1 * Ls + L2) * |(u : ℝ) - (v : ℝ)|) :=
        Finset.sum_le_sum fun l _ => hterm l
    _ = (L1 * Ls + L2) * |(u : ℝ) - (v : ℝ)| := by
        rw [← Finset.sum_mul, hw1, one_mul]

/-! ## The reset occupation -/

/-- Continuity of the reset occupation density of a joint test function along
the flow. -/
theorem ageCounter_jointResetOccupationContinuousAlongFlow (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ a, rate a = 0 → ∀ c, h a c = h 0 c)
    (hsvanish : ∀ a, rate a = 0 → ∀ l, shift l a = 0) (hc : Continuous rate)
    (hcont : Continuous (Function.uncurry h)) (hs : ∀ l, Continuous (shift l)) :
    DavisResetOccupationContinuousAlongFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterJointTest h) := by
  intro z
  have hrw : (fun s : ℝ => davisSegmentResetOccupationDensity
      (ageCounterSHS rate w shift hrate hw) (ageCounterFlow rate w shift hrate hw)
      (ageCounterJointTest h) z s)
      = fun s : ℝ => rate (z.2.1 0 + max s 0) *
          davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
            (ageCounterJointTest h)
            (davisFlow (ageCounterSHS rate w shift hrate hw)
              (ageCounterFlow rate w shift hrate hw) s.toNNReal z) := by
    funext s
    simp only [davisSegmentResetOccupationDensity,
      ageCounter_totalIntensity hrate hw hw1, ageCounter_davisFlow_age,
      Real.coe_toNNReal']
  rw [hrw]
  exact (hc.comp (continuous_const.add (continuous_id.max continuous_const))).mul
    (ageCounter_jointExpectedResetIncrement_continuous hrate hw hw1 hvanish hsvanish
      hcont hs z)

/-- **Regularity of the reset occupation** of a joint test function. -/
theorem ageCounter_jointResetOccupationRegular (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ a, rate a = 0 → ∀ c, h a c = h 0 c)
    (hsvanish : ∀ a, rate a = 0 → ∀ l, shift l a = 0) (hrm : Measurable rate)
    (hc : Continuous rate) (hm : Measurable (Function.uncurry h))
    (hcont : Continuous (Function.uncurry h)) (hsm : ∀ l, Measurable (shift l))
    (hs : ∀ l, Continuous (shift l)) :
    DavisResetOccupationRegular (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterJointTest h) := by
  haveI := ageCounter_intensitiesMeasurable (shift := shift) hrate hw hrm
  exact davisResetOccupationRegular_of_measurable _
    (ageCounter_flowRegular hrate hw) (ageCounter_resetRegular hrate hw hsm)
    (measurable_ageCounterJointTest hm)
    (ageCounter_jointResetOccupationContinuousAlongFlow hrate hw hw1 hvanish
      hsvanish hc hcont hs)

/-! ## The flow integral identity -/

/-- **The flow integral identity for a joint test function**: only the age moves
along the flow, so the flow generator is the partial derivative of `h` in the
age. -/
theorem ageCounter_jointFlowIntegralIdentity {h' : ℝ → ℝ → ℝ}
    (hderiv : ∀ a c, HasDerivAt (fun x => h x c) (h' a c) a)
    (hc' : Continuous (Function.uncurry h')) :
    DavisFlowIntegralIdentity (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (ageCounterJointTest h)
      (ageCounterJointTest h') := by
  intro z u
  have hcongr : Set.EqOn
      (fun s : ℝ => ageCounterJointTest h'
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) s.toNNReal z))
      (fun s : ℝ => h' (z.2.1 0 + s) (z.2.1 1)) (Set.Icc (0 : ℝ) (u : ℝ)) := by
    intro s hs
    show h' ((davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z).2.1 0)
      ((davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z).2.1 1) = _
    rw [ageCounter_davisFlow_age, ageCounter_davisFlow_counter,
      Real.coe_toNNReal _ hs.1]
  have hcontinuous : Continuous fun a : ℝ => h' a (z.2.1 1) :=
    hc'.comp (continuous_id.prodMk continuous_const)
  rw [davisFlowDensityIntegral, setIntegral_congr_fun measurableSet_Icc hcongr,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le u.coe_nonneg,
    intervalIntegral.integral_comp_add_left (fun a => h' a (z.2.1 1)) (z.2.1 0),
    add_zero,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hderiv a (z.2.1 1))
      (hcontinuous.intervalIntegrable _ _)]
  show h ((davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) u z).2.1 0)
    ((davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) u z).2.1 1) -
    h (z.2.1 0) (z.2.1 1) = _
  rw [ageCounter_davisFlow_age, ageCounter_davisFlow_counter]

end JointTest

end SHS
