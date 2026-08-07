import SHSLib.Core.DavisAgeClockModel
import SHSLib.Core.DavisOccupationRegularCriterion
import SHSLib.Core.DavisMarkedJumpBoundedIntensity

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # An age clock with several reset channels

The age clocks of `SHSLib.Core.DavisAgeClockModel` have a single reset channel,
so their conditional channel law is degenerate.  This module builds the family
that exercises several channels.

The state carries two continuous coordinates: the *age* since the last jump,
which grows at unit speed, and a *counter*, which is constant between jumps.
There are `m` reset channels; all of them send the age back to zero — so the
survivor factor of every segment is still the fixed profile of the age clock,
and the holding times still admit a fixed law — but channel `l` moves the
counter by an amount `shift l (age)` depending on the age at which the jump
occurs.  A Boolean mode is toggled as well, so that a reset genuinely moves the
state.

The intensities are *proportional*: `intensity l = w l · rate (age)` with
nonnegative weights summing to one.  Consequently

* the total intensity is `rate (age)`, exactly as for a one-channel age clock;
* the normalized channel weight of channel `l` is the constant `w l` wherever
  the rate does not vanish.

The second point is what makes the family usable with the marked coordinate
noise of `SHSLib.Core.DavisMarkedCoordinateNoise`: the conditional law required
of the mark is a fixed distribution on `Fin m`.

The natural test functions are functions of the counter alone.  Such a function
is constant along the flow, so its flow generator vanishes and the flow integral
identity is trivial; its expected reset increment, on the other hand, mixes all
the channels:

`E[Δg](z) = ∑ l, w l · (h (counter + shift l (age)) − h (counter))`.

For this to be continuous where the rate vanishes — the normalized weights jump
there — the shifts are required to vanish wherever the rate does; this is the
multi-channel form of the compatibility condition of the age clock test
functions.
-/

namespace SHS

/-- The drift of the age–counter model: the age grows at unit speed, the counter
is constant. -/
def ageCounterDrift : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)

/-- The unit vector of the counter coordinate. -/
def counterUnit : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

@[simp] theorem ageCounterDrift_zero : ageCounterDrift 0 = 1 := by simp [ageCounterDrift]

@[simp] theorem ageCounterDrift_one : ageCounterDrift 1 = 0 := by
  simp [ageCounterDrift, EuclideanSpace.single_apply]

@[simp] theorem counterUnit_zero : counterUnit 0 = 0 := by
  simp [counterUnit, EuclideanSpace.single_apply]

@[simp] theorem counterUnit_one : counterUnit 1 = 1 := by simp [counterUnit]

section Model

variable {m : ℕ} {rate : ℝ → ℝ} {w : Fin m → ℝ} {shift : Fin m → ℝ → ℝ}

/-- **The age–counter clock with `m` reset channels.**  Channel `l` fires at
rate `w l · rate (age)`, sends the age back to zero, moves the counter by
`shift l (age)` and toggles the mode. -/
def ageCounterSHS (rate : ℝ → ℝ) (w : Fin m → ℝ) (shift : Fin m → ℝ → ℝ)
    (hrate : ∀ y, 0 ≤ rate y) (hw : ∀ l, 0 ≤ w l) : SHS Bool 2 m where
  f := fun _ _ _ => ageCounterDrift
  phi := fun l q x _ => (!q, (x 1 + shift l (x 0)) • counterUnit)
  intensity := fun l _ x _ => w l * rate (x 0)
  intensity_nonneg := fun l _ x _ => mul_nonneg (hw l) (hrate (x 0))

variable (hrate : ∀ y, 0 ≤ rate y) (hw : ∀ l, 0 ≤ w l)

/-- The flow of the age–counter clock. -/
def ageCounterFlow (rate : ℝ → ℝ) (w : Fin m → ℝ) (shift : Fin m → ℝ → ℝ)
    (hrate : ∀ y, 0 ≤ rate y) (hw : ∀ l, 0 ≤ w l) :
    (ageCounterSHS rate w shift hrate hw).HasGlobalFlow where
  flow := fun t₀ _ x₀ t => x₀ + (max (t - t₀) 0) • ageCounterDrift
  flow_init := by intro t₀ q₀ x₀; simp
  flow_ode := by
    intro t₀ q₀ x₀ t
    have : ∫ _s in Set.Icc t₀ t, (ageCounterSHS rate w shift hrate hw).f q₀
        (x₀ + (max (_s - t₀) 0) • ageCounterDrift) _s
        = (max (t - t₀) 0) • ageCounterDrift := by
      show ∫ _s in Set.Icc t₀ t, ageCounterDrift = _
      rw [setIntegral_const]
      simp [Real.volume_real_Icc]
    rw [this]

@[simp] theorem ageCounter_resetDavisState (l : Fin m) (z : DavisState Bool 2) :
    (ageCounterSHS rate w shift hrate hw).resetDavisState l z
      = (!z.1, (z.2.1 1 + shift l (z.2.1 0)) • counterUnit, z.2.2) := rfl

/-- The age after any reset is zero. -/
@[simp] theorem ageCounter_reset_age (l : Fin m) (z : DavisState Bool 2) :
    ((ageCounterSHS rate w shift hrate hw).resetDavisState l z).2.1 0 = 0 := by
  show ((z.2.1 1 + shift l (z.2.1 0)) • counterUnit) 0 = 0
  simp

/-- The counter after the reset of channel `l`. -/
@[simp] theorem ageCounter_reset_counter (l : Fin m) (z : DavisState Bool 2) :
    ((ageCounterSHS rate w shift hrate hw).resetDavisState l z).2.1 1
      = z.2.1 1 + shift l (z.2.1 0) := by
  show ((z.2.1 1 + shift l (z.2.1 0)) • counterUnit) 1 = _
  simp

/-- Flowing for a duration `u` increases the age by `u`. -/
@[simp] theorem ageCounter_davisFlow_age (u : ℝ≥0) (z : DavisState Bool 2) :
    (davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) u z).2.1 0 = z.2.1 0 + (u : ℝ) := by
  show (z.2.1 + (max (z.2.2 + (u : ℝ) - z.2.2) 0) • ageCounterDrift) 0 = _
  simp

/-- The counter is unchanged along the flow. -/
@[simp] theorem ageCounter_davisFlow_counter (u : ℝ≥0) (z : DavisState Bool 2) :
    (davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) u z).2.1 1 = z.2.1 1 := by
  show (z.2.1 + (max (z.2.2 + (u : ℝ) - z.2.2) 0) • ageCounterDrift) 1 = _
  simp

/-- The mode is unchanged along the flow. -/
@[simp] theorem ageCounter_davisFlow_mode (u : ℝ≥0) (z : DavisState Bool 2) :
    (davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) u z).1 = z.1 := rfl

/-- **The total intensity of the age–counter clock** is the common rate profile
evaluated at the age, provided the weights sum to one. -/
theorem ageCounter_totalIntensity (hw1 : ∑ l, w l = 1) (z : DavisState Bool 2) :
    (ageCounterSHS rate w shift hrate hw).totalIntensity z = rate (z.2.1 0) := by
  show ∑ l : Fin m, w l * rate (z.2.1 0) = _
  rw [← Finset.sum_mul, hw1, one_mul]

/-- The augmented flow of the age–counter clock is regular. -/
theorem ageCounter_flowRegular :
    DavisFlowRegular (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    show Measurable fun z : DavisState Bool 2 =>
      (z.1, z.2.1 + (max (z.2.2 + (u : ℝ) - z.2.2) 0) • ageCounterDrift, z.2.2 + (u : ℝ))
    fun_prop
  · show Measurable fun p : ℝ≥0 × DavisState Bool 2 =>
      (p.2.1, p.2.2.1 + (max (p.2.2.2 + (p.1 : ℝ) - p.2.2.2) 0) • ageCounterDrift,
        p.2.2.2 + (p.1 : ℝ))
    have hcoe : Measurable fun p : ℝ≥0 × DavisState Bool 2 => (p.1 : ℝ) :=
      measurable_coe_nnreal_real.comp measurable_fst
    fun_prop
  · intro s t z
    show ((z.1, z.2.1 + (max (z.2.2 + ((s : ℝ) + (t : ℝ)) - z.2.2) 0) • ageCounterDrift,
        z.2.2 + ((s : ℝ) + (t : ℝ))) : DavisState Bool 2) = _
    show _ = ((z.1, (z.2.1 + (max (z.2.2 + (t : ℝ) - z.2.2) 0) • ageCounterDrift) +
        (max ((z.2.2 + (t : ℝ)) + (s : ℝ) - (z.2.2 + (t : ℝ))) 0) • ageCounterDrift,
        (z.2.2 + (t : ℝ)) + (s : ℝ)) : DavisState Bool 2)
    have hs : (0 : ℝ) ≤ (s : ℝ) := s.coe_nonneg
    have ht : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
    refine Prod.ext rfl (Prod.ext ?_ (by push_cast; ring))
    show z.2.1 + (max (z.2.2 + ((s : ℝ) + (t : ℝ)) - z.2.2) 0) • ageCounterDrift = _
    rw [show z.2.2 + ((s : ℝ) + (t : ℝ)) - z.2.2 = (s : ℝ) + (t : ℝ) by ring,
      show z.2.2 + (t : ℝ) - z.2.2 = (t : ℝ) by ring,
      show (z.2.2 + (t : ℝ)) + (s : ℝ) - (z.2.2 + (t : ℝ)) = (s : ℝ) by ring,
      max_eq_left (by linarith : (0 : ℝ) ≤ (s : ℝ) + (t : ℝ)),
      max_eq_left hs, max_eq_left ht, add_smul]
    abel_nf

/-- The reset channels of the age–counter clock are regular. -/
theorem ageCounter_resetRegular (hshift : ∀ l, Measurable (shift l)) :
    DavisResetRegular (ageCounterSHS rate w shift hrate hw) := by
  refine ⟨?_, ?_⟩
  · intro l
    show Measurable fun z : DavisState Bool 2 =>
      ((!z.1), (z.2.1 1 + shift l (z.2.1 0)) • counterUnit, z.2.2)
    have hsl : Measurable (shift l) := hshift l
    fun_prop
  · intro l z _ h
    have : (!z.1) = z.1 := congrArg (fun y => y.1) h
    exact (Bool.not_ne_self z.1) this

/-- The intensities of the age–counter clock are measurable as soon as the rate
is. -/
theorem ageCounter_intensitiesMeasurable (hm : Measurable rate) :
    (ageCounterSHS rate w shift hrate hw).IntensitiesMeasurable where
  measurable := fun l => by
    have hage : Measurable fun p : Bool × EuclideanSpace ℝ (Fin 2) × ℝ => p.2.1 0 := by
      fun_prop
    exact measurable_const.mul (hm.comp hage)

/-- Every state reached after a jump has age zero, and so does the initial state
if it is chosen with age zero. -/
theorem ageCounter_stateAfterJump_age {Om : Type*} (xi : DavisJumpNoise m Om)
    (initial : DavisState Bool 2) (hinit : initial.2.1 0 = 0) (k : ℕ) (om : Om) :
    (davisStateAfterJump (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) xi initial k om).2.1 0 = 0 := by
  cases k with
  | zero => exact hinit
  | succ k => simp

/-- **The hazard of the age–counter clock is continuous along the flow** as soon
as the rate is continuous. -/
theorem ageCounter_hazardContinuousAlongFlow (hw1 : ∑ l, w l = 1)
    (hc : Continuous rate) :
    DavisHazardContinuousAlongFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) := by
  intro z
  have hrw : (fun s : ℝ => (ageCounterSHS rate w shift hrate hw).totalIntensity
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z))
      = fun s : ℝ => rate (z.2.1 0 + max s 0) := by
    funext s
    simp only [ageCounter_totalIntensity hrate hw hw1, ageCounter_davisFlow_age,
      Real.coe_toNNReal']
  rw [hrw]
  exact hc.comp (continuous_const.add (continuous_id.max continuous_const))

/-- A uniform bound on the rate bounds the total intensity. -/
theorem ageCounter_totalIntensity_le (hw1 : ∑ l, w l = 1) {Lam : ℝ}
    (hL : ∀ y, rate y ≤ Lam) (z : DavisState Bool 2) :
    (ageCounterSHS rate w shift hrate hw).totalIntensity z ≤ Lam := by
  rw [ageCounter_totalIntensity hrate hw hw1]
  exact hL _

/-- **The accumulated hazard of the age–counter clock** is the integral of the
rate along the ages visited by the flow — the same as for a one-channel age
clock. -/
theorem ageCounter_integratedHazard (hw1 : ∑ l, w l = 1) (z : DavisState Bool 2)
    (u : ℝ≥0) :
    davisIntegratedHazard (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) z u
      = ∫ s in Set.Icc (0 : ℝ) (u : ℝ), rate (z.2.1 0 + s) := by
  rw [davisIntegratedHazard]
  refine setIntegral_congr_fun measurableSet_Icc ?_
  intro s hs
  simp only [ageCounter_totalIntensity hrate hw hw1, ageCounter_davisFlow_age,
    Real.coe_toNNReal _ hs.1]

/-- The survivor factor of a segment of the age–counter clock, in closed form,
for a continuous rate. -/
theorem ageCounter_segmentSurvivor (hw1 : ∑ l, w l = 1) (hc : Continuous rate)
    (z : DavisState Bool 2) (u : ℝ≥0) :
    davisSegmentSurvivor (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) z u
      = Real.exp (-(agePrimitive rate (z.2.1 0 + (u : ℝ)) - agePrimitive rate (z.2.1 0))) := by
  rw [davisSegmentSurvivor, ageCounter_integratedHazard hrate hw hw1,
    integral_Icc_comp_add hc _ _ u.coe_nonneg]

end Model

/-! ## Test functions of the counter -/

section TestFunction

variable {m : ℕ} {rate : ℝ → ℝ} {w : Fin m → ℝ} {shift : Fin m → ℝ → ℝ}
  {hfun : ℝ → ℝ} (hrate : ∀ y, 0 ≤ rate y) (hw : ∀ l, 0 ≤ w l)

/-- A test function of the counter alone. -/
def counterTestFunction (hfun : ℝ → ℝ) : DavisState Bool 2 → ℝ := fun z => hfun (z.2.1 1)

theorem measurable_counterTestFunction (hm : Measurable hfun) :
    Measurable (counterTestFunction hfun) := by
  have hcounter : Measurable fun z : DavisState Bool 2 => z.2.1 1 := by fun_prop
  exact hm.comp hcounter

theorem abs_counterTestFunction_le {C : ℝ} (hC : ∀ y, |hfun y| ≤ C)
    (z : DavisState Bool 2) : |counterTestFunction hfun z| ≤ C := hC _

/-- **The expected reset increment of a counter test function** mixes all the
channels.  Where the rate vanishes the shifts are assumed to vanish, so the same
expression is valid everywhere. -/
theorem ageCounter_expectedResetIncrement (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) (z : DavisState Bool 2) :
    davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (counterTestFunction hfun) z
      = ∑ l, w l * (hfun (z.2.1 1 + shift l (z.2.1 0)) - hfun (z.2.1 1)) := by
  rw [davisExpectedResetIncrement]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hval : counterTestFunction hfun
      ((ageCounterSHS rate w shift hrate hw).resetDavisState l z)
      = hfun (z.2.1 1 + shift l (z.2.1 0)) := by
    show hfun (((ageCounterSHS rate w shift hrate hw).resetDavisState l z).2.1 1) = _
    rw [ageCounter_reset_counter]
  have hprob : davisChannelProbability (ageCounterSHS rate w shift hrate hw) z l
      = w l * rate (z.2.1 0) / rate (z.2.1 0) := by
    rw [davisChannelProbability, ageCounter_totalIntensity hrate hw hw1]
    rfl
  rw [hval, hprob]
  by_cases h0 : rate (z.2.1 0) = 0
  · rw [h0, mul_zero, zero_div, zero_mul, hvanish _ h0 l, add_zero, sub_self,
      mul_zero]
  · rw [mul_div_assoc, div_self h0, mul_one]
    rfl

/-- Continuity of the expected reset increment along the flow. -/
theorem ageCounter_expectedResetIncrement_continuous (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) (hf : Continuous hfun)
    (hs : ∀ l, Continuous (shift l)) (z : DavisState Bool 2) :
    Continuous fun s : ℝ => davisExpectedResetIncrement
      (ageCounterSHS rate w shift hrate hw) (counterTestFunction hfun)
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z) := by
  have hrw : (fun s : ℝ => davisExpectedResetIncrement
      (ageCounterSHS rate w shift hrate hw) (counterTestFunction hfun)
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) s.toNNReal z))
      = fun s : ℝ => ∑ l, w l *
          (hfun (z.2.1 1 + shift l (z.2.1 0 + max s 0)) - hfun (z.2.1 1)) := by
    funext s
    simp only [ageCounter_expectedResetIncrement hrate hw hw1 hvanish,
      ageCounter_davisFlow_age, ageCounter_davisFlow_counter, Real.coe_toNNReal']
  rw [hrw]
  refine continuous_finset_sum _ fun l _ => continuous_const.mul ?_
  exact ((hf.comp (continuous_const.add ((hs l).comp
    (continuous_const.add (continuous_id.max continuous_const))))).sub continuous_const)

/-- A Lipschitz test function and Lipschitz shifts give a Lipschitz expected
reset increment along the flow. -/
theorem ageCounter_expectedResetIncrement_lipschitz (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) {Lh Ls : ℝ} (hLh : 0 ≤ Lh)
    (hfL : ∀ y y' : ℝ, |hfun y - hfun y'| ≤ Lh * |y - y'|)
    (hsL : ∀ (l : Fin m) (y y' : ℝ), |shift l y - shift l y'| ≤ Ls * |y - y'|)
    (z : DavisState Bool 2) (u v : ℝ≥0) :
    |davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (counterTestFunction hfun)
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) u z) -
      davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
        (counterTestFunction hfun)
        (davisFlow (ageCounterSHS rate w shift hrate hw)
          (ageCounterFlow rate w shift hrate hw) v z)|
      ≤ (Lh * Ls) * |(u : ℝ) - (v : ℝ)| := by
  set cc := z.2.1 1 with hcc
  set y := z.2.1 0 with hy
  rw [ageCounter_expectedResetIncrement hrate hw hw1 hvanish,
    ageCounter_expectedResetIncrement hrate hw hw1 hvanish,
    ageCounter_davisFlow_age, ageCounter_davisFlow_counter,
    ageCounter_davisFlow_age, ageCounter_davisFlow_counter]
  have hdiff : (∑ l, w l * (hfun (cc + shift l (y + (u : ℝ))) - hfun cc)) -
      (∑ l, w l * (hfun (cc + shift l (y + (v : ℝ))) - hfun cc))
      = ∑ l, w l * (hfun (cc + shift l (y + (u : ℝ))) -
          hfun (cc + shift l (y + (v : ℝ)))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hdiff]
  calc |∑ l, w l * (hfun (cc + shift l (y + (u : ℝ))) -
        hfun (cc + shift l (y + (v : ℝ))))|
      ≤ ∑ l, |w l * (hfun (cc + shift l (y + (u : ℝ))) -
          hfun (cc + shift l (y + (v : ℝ))))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin m, w _l * ((Lh * Ls) * |(u : ℝ) - (v : ℝ)|) := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [abs_mul, abs_of_nonneg (hw l)]
        refine mul_le_mul_of_nonneg_left ?_ (hw l)
        have h1 : |hfun (cc + shift l (y + (u : ℝ))) - hfun (cc + shift l (y + (v : ℝ)))|
            ≤ Lh * |(cc + shift l (y + (u : ℝ))) - (cc + shift l (y + (v : ℝ)))| :=
          hfL _ _
        have h2 : |(cc + shift l (y + (u : ℝ))) - (cc + shift l (y + (v : ℝ)))|
            = |shift l (y + (u : ℝ)) - shift l (y + (v : ℝ))| := by
          congr 1
          ring
        have h3 : |shift l (y + (u : ℝ)) - shift l (y + (v : ℝ))|
            ≤ Ls * |(u : ℝ) - (v : ℝ)| := by
          have := hsL l (y + (u : ℝ)) (y + (v : ℝ))
          rwa [show y + (u : ℝ) - (y + (v : ℝ)) = (u : ℝ) - (v : ℝ) by ring] at this
        calc |hfun (cc + shift l (y + (u : ℝ))) - hfun (cc + shift l (y + (v : ℝ)))|
            ≤ Lh * |shift l (y + (u : ℝ)) - shift l (y + (v : ℝ))| := by
              rw [← h2]; exact h1
          _ ≤ Lh * (Ls * |(u : ℝ) - (v : ℝ)|) := mul_le_mul_of_nonneg_left h3 hLh
          _ = (Lh * Ls) * |(u : ℝ) - (v : ℝ)| := by ring
    _ = (Lh * Ls) * |(u : ℝ) - (v : ℝ)| := by
        rw [← Finset.sum_mul, hw1, one_mul]

/-- The reset occupation density of a counter test function is continuous along
the flow. -/
theorem ageCounter_resetOccupationContinuousAlongFlow (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) (hc : Continuous rate)
    (hf : Continuous hfun) (hs : ∀ l, Continuous (shift l)) :
    DavisResetOccupationContinuousAlongFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (counterTestFunction hfun) := by
  intro z
  have hrw : (fun s : ℝ => davisSegmentResetOccupationDensity
      (ageCounterSHS rate w shift hrate hw) (ageCounterFlow rate w shift hrate hw)
      (counterTestFunction hfun) z s)
      = fun s : ℝ => rate (z.2.1 0 + max s 0) *
          davisExpectedResetIncrement (ageCounterSHS rate w shift hrate hw)
            (counterTestFunction hfun)
            (davisFlow (ageCounterSHS rate w shift hrate hw)
              (ageCounterFlow rate w shift hrate hw) s.toNNReal z) := by
    funext s
    simp only [davisSegmentResetOccupationDensity,
      ageCounter_totalIntensity hrate hw hw1, ageCounter_davisFlow_age,
      Real.coe_toNNReal']
  rw [hrw]
  exact (hc.comp (continuous_const.add (continuous_id.max continuous_const))).mul
    (ageCounter_expectedResetIncrement_continuous hrate hw hw1 hvanish hf hs z)

/-- **Regularity of the reset occupation** of a counter test function, through
the criterion of `SHSLib.Core.DavisOccupationRegularCriterion`. -/
theorem ageCounter_resetOccupationRegular (hw1 : ∑ l, w l = 1)
    (hvanish : ∀ y, rate y = 0 → ∀ l, shift l y = 0) (hrm : Measurable rate)
    (hc : Continuous rate) (hfm : Measurable hfun) (hf : Continuous hfun)
    (hsm : ∀ l, Measurable (shift l)) (hs : ∀ l, Continuous (shift l)) :
    DavisResetOccupationRegular (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (counterTestFunction hfun) := by
  haveI := ageCounter_intensitiesMeasurable (shift := shift) hrate hw hrm
  exact davisResetOccupationRegular_of_measurable _
    (ageCounter_flowRegular hrate hw) (ageCounter_resetRegular hrate hw hsm)
    (measurable_counterTestFunction hfm)
    (ageCounter_resetOccupationContinuousAlongFlow hrate hw hw1 hvanish hc hf hs)

/-- **The flow integral identity for a counter test function**: the counter is
constant along the flow, so the flow generator vanishes. -/
theorem ageCounter_flowIntegralIdentity :
    DavisFlowIntegralIdentity (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) (counterTestFunction hfun)
      (fun _ => 0) := by
  intro z u
  have hl : counterTestFunction hfun
      (davisFlow (ageCounterSHS rate w shift hrate hw)
        (ageCounterFlow rate w shift hrate hw) u z)
      = counterTestFunction hfun z := by
    show hfun ((davisFlow (ageCounterSHS rate w shift hrate hw)
      (ageCounterFlow rate w shift hrate hw) u z).2.1 1) = hfun (z.2.1 1)
    rw [ageCounter_davisFlow_counter]
  rw [hl, sub_self, davisFlowDensityIntegral]
  simp

end TestFunction

end SHS
