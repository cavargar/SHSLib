import SHSLib.Core.DavisAgeClockModel
import SHSLib.Core.DavisMarkedJumpBoundedIntensity

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Test functions of the age for an age clock

The model-level martingale and Dynkin statements ask, besides the two
conditional laws, for a package of regularity conditions on the pair (model,
test function): continuity of the hazard along the flow, continuity and
measurability of the reset occupation density, the flow integral identity
relating the test function to its flow generator, and continuity together with
a Lipschitz bound for the expected reset increment along the flow.

For the age clocks of `SHSLib.Core.DavisAgeClockModel` all of them follow from
one-dimensional data.  A test function of the *age* alone, `g z = hfun (age z)`,
has

* expected reset increment `hfun 0 - hfun (age)`, provided `hfun` is constant
  equal to `hfun 0` wherever the rate vanishes — the normalized channel weight
  is one exactly where the rate does not vanish, and where it does vanish the
  increment is zero anyway;
* reset occupation density `(hfun 0 - hfun (age)) · rate (age)`;
* flow integral identity with flow generator `a z = hfun' (age z)`, by the
  fundamental theorem of calculus.

This module proves all of these, so that a concrete age clock only has to
exhibit a rate and a one-dimensional test function.
-/

namespace SHS

/-- A test function of the age alone. -/
def ageTestFunction (hfun : ℝ → ℝ) : DavisState Bool 1 → ℝ := fun z => hfun (z.2.1 0)

theorem measurable_ageTestFunction {hfun : ℝ → ℝ} (hm : Measurable hfun) :
    Measurable (ageTestFunction hfun) := by
  have hage : Measurable fun z : DavisState Bool 1 => z.2.1 0 := by fun_prop
  exact hm.comp hage

theorem abs_ageTestFunction_le {hfun : ℝ → ℝ} {C : ℝ} (hC : ∀ y, |hfun y| ≤ C)
    (z : DavisState Bool 1) : |ageTestFunction hfun z| ≤ C := hC _

@[simp] theorem ageTestFunction_reset {rate : ℝ → ℝ} (hrate : ∀ y, 0 ≤ rate y)
    (hfun : ℝ → ℝ) (ℓ : Fin 1) (z : DavisState Bool 1) :
    ageTestFunction hfun ((ageClockSHS rate hrate).resetDavisState ℓ z) = hfun 0 := by
  show hfun (((ageClockSHS rate hrate).resetDavisState ℓ z).2.1 0) = hfun 0
  rw [ageClock_reset_age]

/-! ## The expected reset increment -/

/-- **The expected reset increment of an age test function.**  Where the rate
vanishes the test function is assumed to agree with its value at age zero, so
the increment is the same expression everywhere. -/
theorem ageClock_expectedResetIncrement {rate hfun : ℝ → ℝ}
    (hrate : ∀ y, 0 ≤ rate y) (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0)
    (z : DavisState Bool 1) :
    davisExpectedResetIncrement (ageClockSHS rate hrate) (ageTestFunction hfun) z
      = hfun 0 - hfun (z.2.1 0) := by
  rw [davisExpectedResetIncrement, Fin.sum_univ_one,
    ageTestFunction_reset hrate hfun 0 z]
  have hprob : davisChannelProbability (ageClockSHS rate hrate) z 0
      = rate (z.2.1 0) / rate (z.2.1 0) := by
    rw [davisChannelProbability, ageClock_totalIntensity]
    rfl
  rw [hprob]
  by_cases h0 : rate (z.2.1 0) = 0
  · rw [h0, div_zero, zero_mul, hvanish _ h0, sub_self]
  · rw [div_self h0, one_mul]
    rfl

/-- Continuity of the expected reset increment along the flow. -/
theorem ageClock_expectedResetIncrement_continuous {rate hfun : ℝ → ℝ}
    (hrate : ∀ y, 0 ≤ rate y) (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0)
    (hf : Continuous hfun) (z : DavisState Bool 1) :
    Continuous fun s : ℝ => davisExpectedResetIncrement (ageClockSHS rate hrate)
      (ageTestFunction hfun)
      (davisFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate) s.toNNReal z) := by
  have hrw : (fun s : ℝ => davisExpectedResetIncrement (ageClockSHS rate hrate)
      (ageTestFunction hfun)
      (davisFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate) s.toNNReal z))
      = fun s : ℝ => hfun 0 - hfun (z.2.1 0 + max s 0) := by
    funext s
    rw [ageClock_expectedResetIncrement hrate hvanish, ageClock_davisFlow_age,
      Real.coe_toNNReal']
  rw [hrw]
  exact continuous_const.sub (hf.comp (continuous_const.add
    (continuous_id.max continuous_const)))

/-- A Lipschitz test function of the age gives a Lipschitz expected reset
increment along the flow. -/
theorem ageClock_expectedResetIncrement_lipschitz {rate hfun : ℝ → ℝ}
    (hrate : ∀ y, 0 ≤ rate y) (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0)
    {L : ℝ} (hL : ∀ y y' : ℝ, |hfun y - hfun y'| ≤ L * |y - y'|)
    (z : DavisState Bool 1) (u v : ℝ≥0) :
    |davisExpectedResetIncrement (ageClockSHS rate hrate) (ageTestFunction hfun)
        (davisFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate) u z) -
      davisExpectedResetIncrement (ageClockSHS rate hrate) (ageTestFunction hfun)
        (davisFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate) v z)|
      ≤ L * |(u : ℝ) - (v : ℝ)| := by
  rw [ageClock_expectedResetIncrement hrate hvanish,
    ageClock_expectedResetIncrement hrate hvanish, ageClock_davisFlow_age,
    ageClock_davisFlow_age]
  have hsub : (hfun 0 - hfun (z.2.1 0 + (u : ℝ))) - (hfun 0 - hfun (z.2.1 0 + (v : ℝ)))
      = hfun (z.2.1 0 + (v : ℝ)) - hfun (z.2.1 0 + (u : ℝ)) := by ring
  rw [hsub]
  have := hL (z.2.1 0 + (v : ℝ)) (z.2.1 0 + (u : ℝ))
  have habs : |z.2.1 0 + (v : ℝ) - (z.2.1 0 + (u : ℝ))| = |(u : ℝ) - (v : ℝ)| := by
    rw [show z.2.1 0 + (v : ℝ) - (z.2.1 0 + (u : ℝ)) = -((u : ℝ) - (v : ℝ)) by ring,
      abs_neg]
  rwa [habs] at this

/-! ## The reset occupation density -/

/-- **The reset occupation density of an age test function.** -/
theorem ageClock_resetOccupationDensity {rate hfun : ℝ → ℝ}
    (hrate : ∀ y, 0 ≤ rate y) (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0)
    (z : DavisState Bool 1) (s : ℝ) :
    davisSegmentResetOccupationDensity (ageClockSHS rate hrate)
        (ageClockFlow rate hrate) (ageTestFunction hfun) z s
      = (hfun 0 - hfun (z.2.1 0 + max s 0)) * rate (z.2.1 0 + max s 0) := by
  rw [davisSegmentResetOccupationDensity, ageClock_expectedResetIncrement hrate hvanish,
    ageClock_totalIntensity, ageClock_davisFlow_age, Real.coe_toNNReal']
  ring

/-- The occupation density of an age test function, as a function of the age
alone. -/
def ageOccupationDensity (rate hfun : ℝ → ℝ) (y : ℝ) : ℝ :=
  (hfun 0 - hfun y) * rate y

theorem continuous_ageOccupationDensity {rate hfun : ℝ → ℝ} (hr : Continuous rate)
    (hf : Continuous hfun) : Continuous (ageOccupationDensity rate hfun) :=
  (continuous_const.sub hf).mul hr

/-- Continuity of the reset occupation density along the flow. -/
theorem ageClock_resetOccupationContinuousAlongFlow {rate hfun : ℝ → ℝ}
    (hrate : ∀ y, 0 ≤ rate y) (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0)
    (hr : Continuous rate) (hf : Continuous hfun) :
    DavisResetOccupationContinuousAlongFlow (ageClockSHS rate hrate)
      (ageClockFlow rate hrate) (ageTestFunction hfun) := by
  intro z
  have hrw : davisSegmentResetOccupationDensity (ageClockSHS rate hrate)
      (ageClockFlow rate hrate) (ageTestFunction hfun) z
      = fun s : ℝ => ageOccupationDensity rate hfun (z.2.1 0 + max s 0) :=
    funext fun s => ageClock_resetOccupationDensity hrate hvanish z s
  rw [hrw]
  exact (continuous_ageOccupationDensity hr hf).comp
    (continuous_const.add (continuous_id.max continuous_const))

/-- The reset occupation compensator of an age test function in closed form. -/
theorem ageClock_resetOccupationCompensator {rate hfun : ℝ → ℝ}
    (hrate : ∀ y, 0 ≤ rate y) (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0)
    (hr : Continuous rate) (hf : Continuous hfun) (z : DavisState Bool 1) (u : ℝ≥0) :
    davisSegmentResetOccupationCompensator (ageClockSHS rate hrate)
        (ageClockFlow rate hrate) (ageTestFunction hfun) z u
      = agePrimitive (ageOccupationDensity rate hfun) (z.2.1 0 + (u : ℝ)) -
          agePrimitive (ageOccupationDensity rate hfun) (z.2.1 0) := by
  rw [davisSegmentResetOccupationCompensator]
  have hcongr : Set.EqOn
      (fun s : ℝ => davisSegmentResetOccupationDensity (ageClockSHS rate hrate)
        (ageClockFlow rate hrate) (ageTestFunction hfun) z s)
      (fun s : ℝ => ageOccupationDensity rate hfun (z.2.1 0 + s))
      (Set.Icc (0 : ℝ) (u : ℝ)) := by
    intro s hs
    show davisSegmentResetOccupationDensity (ageClockSHS rate hrate)
      (ageClockFlow rate hrate) (ageTestFunction hfun) z s
        = ageOccupationDensity rate hfun (z.2.1 0 + s)
    rw [ageClock_resetOccupationDensity hrate hvanish z s, max_eq_left hs.1]
    rfl
  rw [setIntegral_congr_fun measurableSet_Icc hcongr,
    integral_Icc_comp_add (continuous_ageOccupationDensity hr hf) _ _ u.coe_nonneg]

/-- **The reset occupation regularity of an age test function.** -/
theorem ageClock_resetOccupationRegular {rate hfun : ℝ → ℝ}
    (hrate : ∀ y, 0 ≤ rate y) (hvanish : ∀ y, rate y = 0 → hfun y = hfun 0)
    (hr : Continuous rate) (hf : Continuous hfun) :
    DavisResetOccupationRegular (ageClockSHS rate hrate) (ageClockFlow rate hrate)
      (ageTestFunction hfun) := by
  have hage : Measurable fun z : DavisState Bool 1 => z.2.1 0 := by fun_prop
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hrw : (fun p : DavisState Bool 1 × ℝ =>
        davisSegmentResetOccupationDensity (ageClockSHS rate hrate)
          (ageClockFlow rate hrate) (ageTestFunction hfun) p.1 p.2)
        = fun p : DavisState Bool 1 × ℝ =>
          ageOccupationDensity rate hfun (p.1.2.1 0 + max p.2 0) := by
      funext p
      exact ageClock_resetOccupationDensity hrate hvanish p.1 p.2
    rw [hrw]
    refine (continuous_ageOccupationDensity hr hf).measurable.comp ?_
    exact (hage.comp measurable_fst).add (measurable_snd.max measurable_const)
  · intro z u
    have hint : IntegrableOn
        (fun s : ℝ => ageOccupationDensity rate hfun (z.2.1 0 + max s 0))
        (Set.Icc (0 : ℝ) (u : ℝ)) :=
      ((continuous_ageOccupationDensity hr hf).comp
        (continuous_const.add (continuous_id.max continuous_const))).integrableOn_Icc
    exact hint.congr_fun
      (fun s _ => (ageClock_resetOccupationDensity hrate hvanish z s).symm)
      measurableSet_Icc
  · have hrw : (fun p : DavisState Bool 1 × ℝ≥0 =>
        davisSegmentResetOccupationCompensator (ageClockSHS rate hrate)
          (ageClockFlow rate hrate) (ageTestFunction hfun) p.1 p.2)
        = fun p : DavisState Bool 1 × ℝ≥0 =>
          agePrimitive (ageOccupationDensity rate hfun) (p.1.2.1 0 + (p.2 : ℝ)) -
            agePrimitive (ageOccupationDensity rate hfun) (p.1.2.1 0) := by
      funext p
      exact ageClock_resetOccupationCompensator hrate hvanish hr hf p.1 p.2
    rw [hrw]
    have hcoe : Measurable fun p : DavisState Bool 1 × ℝ≥0 => (p.2 : ℝ) :=
      measurable_coe_nnreal_real.comp measurable_snd
    have hP := (continuous_agePrimitive
      (continuous_ageOccupationDensity hr hf)).measurable
    exact (hP.comp ((hage.comp measurable_fst).add hcoe)).sub
      (hP.comp (hage.comp measurable_fst))
  · have hrw : (fun p : DavisState Bool 1 × ℝ≥0 =>
        davisSegmentSurvivor (ageClockSHS rate hrate) (ageClockFlow rate hrate)
          p.1 p.2)
        = fun p : DavisState Bool 1 × ℝ≥0 =>
          Real.exp (-(agePrimitive rate (p.1.2.1 0 + (p.2 : ℝ)) -
            agePrimitive rate (p.1.2.1 0))) := by
      funext p
      rw [davisSegmentSurvivor, ageClock_integratedHazard_eq_primitive hrate hr]
    rw [hrw]
    have hcoe : Measurable fun p : DavisState Bool 1 × ℝ≥0 => (p.2 : ℝ) :=
      measurable_coe_nnreal_real.comp measurable_snd
    have hP := (continuous_agePrimitive hr).measurable
    exact Real.measurable_exp.comp
      (((hP.comp ((hage.comp measurable_fst).add hcoe)).sub
        (hP.comp (hage.comp measurable_fst))).neg)

/-! ## The flow integral identity -/

/-- **The flow integral identity for an age test function**, with the derivative
of the one-dimensional profile as flow generator. -/
theorem ageClock_flowIntegralIdentity {rate hfun hfun' : ℝ → ℝ}
    (hrate : ∀ y, 0 ≤ rate y) (hderiv : ∀ y, HasDerivAt hfun (hfun' y) y)
    (hc : Continuous hfun') :
    DavisFlowIntegralIdentity (ageClockSHS rate hrate) (ageClockFlow rate hrate)
      (ageTestFunction hfun) (ageTestFunction hfun') := by
  intro z u
  have hcongr : Set.EqOn
      (fun s : ℝ => ageTestFunction hfun'
        (davisFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate) s.toNNReal z))
      (fun s : ℝ => hfun' (z.2.1 0 + s)) (Set.Icc (0 : ℝ) (u : ℝ)) := by
    intro s hs
    show hfun' ((davisFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate)
      s.toNNReal z).2.1 0) = _
    rw [ageClock_davisFlow_age, Real.coe_toNNReal _ hs.1]
  rw [davisFlowDensityIntegral, setIntegral_congr_fun measurableSet_Icc hcongr,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le u.coe_nonneg,
    intervalIntegral.integral_comp_add_left hfun' (z.2.1 0), add_zero,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y)
      (hc.intervalIntegrable _ _)]
  show hfun ((davisFlow (ageClockSHS rate hrate) (ageClockFlow rate hrate) u z).2.1 0)
    - hfun (z.2.1 0) = _
  rw [ageClock_davisFlow_age]

end SHS
