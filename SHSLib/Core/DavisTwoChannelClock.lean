import SHSLib.Core.DavisAgeCounterModel
import SHSLib.Core.DavisMarkedCoordinateNoise
import SHSLib.Core.DavisRampedClockNoise
import SHSLib.Core.DavisNonExplosiveLowerBound

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # A two-channel refractory clock, and its Dynkin identity

This module assembles the previous batches into the first Davis instance with
*two* reset channels, for which every hypothesis of the model-level statements
is proved rather than assumed.

* **The model** is the age–counter clock of `SHSLib.Core.DavisAgeCounterModel`
  at the ramped rate of `SHSLib.Core.DavisRampedClockModel`: the age grows at
  unit speed and the intensity `lam · min (max (age − dd) 0) 1` vanishes below
  the dead time `dd`.  Both channels zero the age and toggle the mode; channel
  `0` increases the counter by the bump profile `rampProfile dd (age)`, channel
  `1` decreases it by the same amount.  The channels carry the constant weights
  `p` and `1 − p`.
* **The noise** is the marked coordinate noise of
  `SHSLib.Core.DavisMarkedCoordinateNoise`: the even coordinates carry unit
  exponential samples, read out by the inverse-transform map of the ramped
  clock, and the odd coordinates carry a two-point law, read out into the two
  marks with probabilities `p` and `1 − p`.
* **The test function** is the cosine of the counter: bounded by one,
  one-Lipschitz, and constant along the flow.

Both conditional laws hold: the holding-time law because every channel zeroes
the age, so every segment has the survivor factor of the ramped clock; the
channel law because the marks are independent of everything drawn before them
and the normalized channel weights are the constants `p` and `1 − p` at the
realized pre-jump states, which are beyond the dead time.

The conclusions are the Dynkin identity and the martingale property of the
occupation-compensated test-function process, with no hypotheses beyond
`0 < lam`, `0 < dd` and `0 ≤ p ≤ 1`.
-/

namespace SHS

/-! ## The two-point mark law -/

/-- The two-point law giving mass `p` to `-1` and `1 - p` to `1`. -/
def twoPointMeasure (p : ℝ) : Measure ℝ :=
  ENNReal.ofReal p • Measure.dirac (-1) + ENNReal.ofReal (1 - p) • Measure.dirac 1

theorem isProbabilityMeasure_twoPointMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (twoPointMeasure p) := by
  constructor
  simp only [twoPointMeasure, Measure.coe_add, Pi.add_apply, Measure.coe_smul,
    Pi.smul_apply, Measure.dirac_apply', MeasurableSet.univ, Set.indicator_univ,
    smul_eq_mul, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_add hp0 (by linarith)]
  simp

/-- The readout of a mark from the odd coordinate. -/
def markReadout : ℝ → Fin 2 := fun x => if x ≤ 0 then 0 else 1

theorem measurable_markReadout : Measurable markReadout :=
  Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

/-- The mark `0` has probability `p`. -/
theorem twoPointMeasure_markReadout_zero (p : ℝ) :
    twoPointMeasure p {x : ℝ | markReadout x = 0} = ENNReal.ofReal p := by
  have hset : {x : ℝ | markReadout x = 0} = Set.Iic 0 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Iic, markReadout]
    split <;> simp_all
  rw [hset, twoPointMeasure]
  simp [Measure.dirac_apply']

/-- The mark `1` has probability `1 - p`. -/
theorem twoPointMeasure_markReadout_one (p : ℝ) :
    twoPointMeasure p {x : ℝ | markReadout x = 1} = ENNReal.ofReal (1 - p) := by
  have hset : {x : ℝ | markReadout x = 1} = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, markReadout]
    split <;> simp_all
  rw [hset, twoPointMeasure]
  simp [Measure.dirac_apply']

/-! ## The two channels -/

/-- The weights of the two channels. -/
def twoWeights (p : ℝ) : Fin 2 → ℝ := ![p, 1 - p]

/-- The counter shifts of the two channels: plus and minus the bump profile of
the age. -/
def twoShifts (d : ℝ) : Fin 2 → ℝ → ℝ := ![rampProfile d, fun y => -rampProfile d y]

theorem twoWeights_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ l, 0 ≤ twoWeights p l := by
  intro l
  fin_cases l <;> simp [twoWeights] <;> linarith

theorem twoWeights_sum (p : ℝ) : ∑ l, twoWeights p l = 1 := by
  simp [twoWeights, Fin.sum_univ_two]

@[simp] theorem twoWeights_zero (p : ℝ) : twoWeights p 0 = p := rfl

@[simp] theorem twoWeights_one (p : ℝ) : twoWeights p 1 = 1 - p := rfl

theorem twoShifts_measurable (d : ℝ) : ∀ l, Measurable (twoShifts d l) := by
  intro l
  fin_cases l
  · exact (continuous_rampProfile d).measurable
  · exact (continuous_rampProfile d).neg.measurable

theorem twoShifts_continuous (d : ℝ) : ∀ l, Continuous (twoShifts d l) := by
  intro l
  fin_cases l
  · exact continuous_rampProfile d
  · exact (continuous_rampProfile d).neg

theorem twoShifts_lipschitz (d : ℝ) :
    ∀ (l : Fin 2) (y y' : ℝ), |twoShifts d l y - twoShifts d l y'| ≤ 1 * |y - y'| := by
  intro l y y'
  fin_cases l
  · exact rampProfile_lipschitz d y y'
  · show |(-rampProfile d y) - (-rampProfile d y')| ≤ 1 * |y - y'|
    rw [show (-rampProfile d y) - (-rampProfile d y')
      = -(rampProfile d y - rampProfile d y') by ring, abs_neg]
    exact rampProfile_lipschitz d y y'

/-- Both shifts vanish where the ramped rate vanishes: the compatibility
condition of the counter test functions. -/
theorem twoShifts_vanish {lam d : ℝ} (hlam : 0 < lam) (y : ℝ) :
    rampRate lam d y = 0 → ∀ l, twoShifts d l y = 0 := by
  intro h l
  have hy : rampProfile d y = 0 :=
    rampProfile_eq_zero_of_le ((rampRate_eq_zero_iff hlam d y).1 h)
  fin_cases l
  · exact hy
  · show -rampProfile d y = 0
    rw [hy, neg_zero]

/-! ## The model and its test function -/

section TwoChannel

variable {lam : ℝ} (hlam : 0 < lam) {dd : ℝ≥0} (hdd : 0 < dd) {p : ℝ}
  (hp0 : 0 ≤ p) (hp1 : p ≤ 1)

/-- **The two-channel refractory clock.** -/
abbrev twoChannelModel (lam : ℝ) (hlam : 0 < lam) (dd : ℝ≥0) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : SHS Bool 2 2 :=
  ageCounterSHS (rampRate lam (dd : ℝ)) (twoWeights p) (twoShifts (dd : ℝ))
    (rampRate_nonneg hlam.le (dd : ℝ)) (twoWeights_nonneg hp0 hp1)

/-- Its flow. -/
abbrev twoChannelFlow (lam : ℝ) (hlam : 0 < lam) (dd : ℝ≥0) (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : (twoChannelModel lam hlam dd p hp0 hp1).HasGlobalFlow :=
  ageCounterFlow (rampRate lam (dd : ℝ)) (twoWeights p) (twoShifts (dd : ℝ))
    (rampRate_nonneg hlam.le (dd : ℝ)) (twoWeights_nonneg hp0 hp1)

/-- The test function: the cosine of the counter. -/
def twoChannelTest : DavisState Bool 2 → ℝ := counterTestFunction Real.cos

theorem measurable_twoChannelTest : Measurable twoChannelTest :=
  measurable_counterTestFunction Real.continuous_cos.measurable

theorem abs_twoChannelTest_le (z : DavisState Bool 2) : |twoChannelTest z| ≤ 1 :=
  abs_counterTestFunction_le (fun y => Real.abs_cos_le_one y) z

theorem cos_lipschitz (y y' : ℝ) : |Real.cos y - Real.cos y'| ≤ 1 * |y - y'| := by
  have := Real.lipschitzWith_cos.dist_le_mul y y'
  rw [Real.dist_eq, Real.dist_eq] at this
  simpa using this

/-- The initial state: age zero, counter zero, clock `t₀`. -/
def twoChannelInitial (t₀ : ℝ) : DavisState Bool 2 := (true, 0, t₀)

@[simp] theorem twoChannelInitial_age (t₀ : ℝ) : (twoChannelInitial t₀).2.1 0 = 0 := by
  simp [twoChannelInitial]

include hlam in
/-- **The survivor factor of a segment started at age zero** is the survivor
factor of the ramped clock. -/
theorem twoChannel_segmentSurvivor (z : DavisState Bool 2) (hz : z.2.1 0 = 0)
    (u : ℝ≥0) :
    davisSegmentSurvivor (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1) z u
      = Real.exp (-rampedHazard lam (dd : ℝ) (u : ℝ)) := by
  rw [davisSegmentSurvivor,
    ageCounter_integratedHazard (rampRate_nonneg hlam.le (dd : ℝ))
      (twoWeights_nonneg hp0 hp1) (twoWeights_sum p) z u, hz]
  simp only [zero_add]
  rw [integral_rampRate lam dd.coe_nonneg u.coe_nonneg]

/-! ## The noise -/

/-- The noise of the two-channel clock: the ramped holding times on the even
coordinates, the two-point marks on the odd ones. -/
abbrev twoChannelNoise (lam : ℝ) (dd : ℝ≥0) : DavisJumpNoise 2 (ℕ → ℝ) :=
  markedCoordinateNoise (rampedHolding lam dd) markReadout

theorem twoChannelNoise_measurable (lam : ℝ) (dd : ℝ≥0) :
    (twoChannelNoise lam dd).MeasurableNoise :=
  markedCoordinateNoise_measurable (measurable_rampedHolding lam dd)
    measurable_markReadout

/-- Every holding time of the two-channel noise is at least the dead time. -/
theorem le_twoChannelNoise_holdingTime (lam : ℝ) (dd : ℝ≥0) (k : ℕ) (om : ℕ → ℝ) :
    dd ≤ (twoChannelNoise lam dd).holdingTime k om :=
  le_rampedHolding lam dd (om (2 * k))

include hdd in
/-- The two-channel noise does not explode. -/
theorem twoChannel_nonExplosive : (twoChannelNoise lam dd).NonExplosive :=
  DavisJumpNoise.nonExplosive_of_holdingTime_ge _ dd hdd
    (le_twoChannelNoise_holdingTime lam dd)

/-- The law of the two-channel instance. -/
def twoChannelMeasure (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure (ℕ → ℝ) :=
  @interleavedPathMeasure (expMeasure 1) (twoPointMeasure p)
    (isProbabilityMeasure_expMeasure one_pos)
    (isProbabilityMeasure_twoPointMeasure hp0 hp1)

instance isProbabilityMeasure_twoChannelMeasure {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (twoChannelMeasure p hp0 hp1) := by
  haveI := isProbabilityMeasure_expMeasure (one_pos : (0 : ℝ) < 1)
  haveI := isProbabilityMeasure_twoPointMeasure hp0 hp1
  rw [twoChannelMeasure]
  infer_instance

/-- The intensities of the two-channel clock are measurable. -/
theorem twoChannel_intensitiesMeasurable :
    (twoChannelModel lam hlam dd p hp0 hp1).IntensitiesMeasurable :=
  ageCounter_intensitiesMeasurable (shift := twoShifts (dd : ℝ))
    (rampRate_nonneg hlam.le (dd : ℝ)) (twoWeights_nonneg hp0 hp1)
    (continuous_rampRate lam (dd : ℝ)).measurable

include hlam in
/-- **The conditional holding-time law holds for the two-channel instance.** -/
theorem twoChannel_conditionalHoldingTimeLaw (t₀ : ℝ) :
    (twoChannelNoise lam dd).ConditionalHoldingTimeLaw
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (ageCounter_flowRegular _ _) (ageCounter_resetRegular _ _ (twoShifts_measurable _))
      (twoChannelMeasure p hp0 hp1) (twoChannelNoise_measurable lam dd)
      (twoChannelInitial t₀) := by
  haveI := isProbabilityMeasure_expMeasure (one_pos : (0 : ℝ) < 1)
  haveI := isProbabilityMeasure_twoPointMeasure hp0 hp1
  rw [twoChannelMeasure]
  refine markedCoordinateNoise_conditionalHoldingTimeLaw _ _ _ _ (expMeasure 1)
    (twoPointMeasure p) (measurable_rampedHolding lam dd) measurable_markReadout
    (twoChannelInitial t₀)
    (fun u => Real.exp (-rampedHazard lam (dd : ℝ) (u : ℝ))) ?_ ?_
  · intro k om u
    refine twoChannel_segmentSurvivor hlam hp0 hp1 _ ?_ u
    exact ageCounter_stateAfterJump_age _ _ _ _ (twoChannelInitial_age t₀) _ om
  · intro u
    exact expMeasure_one_rampedHolding_gt hlam dd u

include hp0 hp1 in
/-- Almost surely the even coordinate is positive, so the age reached just
before a jump is strictly beyond the dead time. -/
theorem twoChannel_ae_pos (k : ℕ) :
    ∀ᵐ om ∂(twoChannelMeasure p hp0 hp1), 0 < om (2 * k) := by
  haveI := isProbabilityMeasure_expMeasure (one_pos : (0 : ℝ) < 1)
  haveI := isProbabilityMeasure_twoPointMeasure hp0 hp1
  have hnull : twoChannelMeasure p hp0 hp1 {om : ℕ → ℝ | om (2 * k) ∈ Set.Iic (0 : ℝ)}
      = 0 := by
    rw [twoChannelMeasure,
      interleavedPathMeasure_coordinate (expMeasure 1) (twoPointMeasure p) (2 * k)
        measurableSet_Iic, interleavedLaw_even]
    exact expMeasure_one_Iic_zero
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro om hom
  simpa using le_of_not_gt hom

include hlam hp0 hp1 in
/-- **The conditional channel law holds for the two-channel instance.**  The
marks are independent of everything drawn before them, and the normalized
channel weights at the realized pre-jump states are the constants `p` and
`1 - p`. -/
theorem twoChannel_conditionalChannelLaw (t₀ : ℝ) :
    (twoChannelNoise lam dd).ConditionalChannelLaw
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelMeasure p hp0 hp1) (twoChannelInitial t₀) := by
  haveI := isProbabilityMeasure_expMeasure (one_pos : (0 : ℝ) < 1)
  haveI := isProbabilityMeasure_twoPointMeasure hp0 hp1
  have hlaw : ∀ (k : ℕ) (l : Fin 2),
      ∀ᵐ om ∂(twoChannelMeasure p hp0 hp1), ENNReal.ofReal
        (davisChannelProbability (twoChannelModel lam hlam dd p hp0 hp1)
          ((davisPreJumpHistory (twoChannelModel lam hlam dd p hp0 hp1)
            (twoChannelFlow lam hlam dd p hp0 hp1) (twoChannelNoise lam dd)
            (twoChannelInitial t₀) k om).stateBeforeNextJump
              (twoChannelModel lam hlam dd p hp0 hp1)
              (twoChannelFlow lam hlam dd p hp0 hp1)
              ((twoChannelNoise lam dd).holdingTime k om)) l)
          = twoPointMeasure p {x : ℝ | markReadout x = l} := by
    intro k l
    filter_upwards [twoChannel_ae_pos hp0 hp1 k] with om hom
    set z := (davisPreJumpHistory (twoChannelModel lam hlam dd p hp0 hp1)
      (twoChannelFlow lam hlam dd p hp0 hp1) (twoChannelNoise lam dd)
      (twoChannelInitial t₀) k om).stateBeforeNextJump
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        ((twoChannelNoise lam dd).holdingTime k om) with hz
    have hage : z.2.1 0 = ((twoChannelNoise lam dd).holdingTime k om : ℝ) := by
      rw [hz, DavisPreJumpHistory.stateBeforeNextJump,
        ageCounter_davisFlow_age,
        show (davisPreJumpHistory (twoChannelModel lam hlam dd p hp0 hp1)
          (twoChannelFlow lam hlam dd p hp0 hp1) (twoChannelNoise lam dd)
          (twoChannelInitial t₀) k om).currentState.2.1 0 = 0 from
          ageCounter_stateAfterJump_age _ _ _ _ (twoChannelInitial_age t₀) _ om]
      ring
    have hgt : (dd : ℝ) < z.2.1 0 := by
      rw [hage, show (twoChannelNoise lam dd).holdingTime k om
        = rampedHolding lam dd (om (2 * k)) from rfl, rampedHolding]
      push_cast
      have := rampedHoldingProfile_pos hlam hom
      rw [Real.coe_toNNReal _ this.le]
      linarith
    have hrate : rampRate lam (dd : ℝ) (z.2.1 0) ≠ 0 := by
      intro h
      exact absurd ((rampRate_eq_zero_iff hlam (dd : ℝ) (z.2.1 0)).1 h) (not_le.2 hgt)
    have hprob : davisChannelProbability (twoChannelModel lam hlam dd p hp0 hp1) z l
        = twoWeights p l := by
      rw [davisChannelProbability,
        ageCounter_totalIntensity (rampRate_nonneg hlam.le (dd : ℝ))
          (twoWeights_nonneg hp0 hp1) (twoWeights_sum p) z]
      show twoWeights p l * rampRate lam (dd : ℝ) (z.2.1 0)
        / rampRate lam (dd : ℝ) (z.2.1 0) = _
      rw [mul_div_assoc, div_self hrate, mul_one]
    rw [hprob]
    fin_cases l
    · show ENNReal.ofReal (twoWeights p 0)
        = twoPointMeasure p {x : ℝ | markReadout x = 0}
      rw [twoPointMeasure_markReadout_zero, twoWeights_zero]
    · show ENNReal.ofReal (twoWeights p 1)
        = twoPointMeasure p {x : ℝ | markReadout x = 1}
      rw [twoPointMeasure_markReadout_one, twoWeights_one]
  rw [twoChannelMeasure] at hlaw ⊢
  exact markedCoordinateNoise_conditionalChannelLaw _ _ (ageCounter_flowRegular _ _)
    (ageCounter_resetRegular _ _ (twoShifts_measurable _)) (expMeasure 1)
    (twoPointMeasure p) (measurable_rampedHolding lam dd) measurable_markReadout
    (twoChannelInitial t₀) hlaw

/-! ## The conclusions

Both are proved for an arbitrary bounded Lipschitz profile of the counter; the
cosine of the counter is the special case used as the running example.
-/

section Profile

variable {hfun : ℝ → ℝ} {C Lh : ℝ}

set_option maxHeartbeats 1000000 in
include hlam hdd hp0 hp1 in
/-- **The Dynkin identity on the two-channel refractory clock**, for a bounded
Lipschitz profile of the counter: the occupation-compensated increment has zero
mean at every elapsed time. -/
theorem twoChannel_dynkin_of_profile (hfm : Measurable hfun) (hfc : Continuous hfun)
    (hC : ∀ y, |hfun y| ≤ C) (hLh0 : 0 ≤ Lh)
    (hL : ∀ y y' : ℝ, |hfun y - hfun y'| ≤ Lh * |y - y'|) (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (fun _ => 0) (counterTestFunction hfun) t om
      ∂(twoChannelMeasure p hp0 hp1) = 0 := by
  haveI : (twoChannelModel lam hlam dd p hp0 hp1).IntensitiesMeasurable :=
    twoChannel_intensitiesMeasurable hlam hp0 hp1
  exact integral_davisElapsedCompensatedGeneratorProcess_eq_zero_markedJump_of_boundedIntensity
    (hf := ageCounter_flowRegular _ _)
    (hr := ageCounter_resetRegular _ _ (twoShifts_measurable _))
    (hξ := twoChannelNoise_measurable lam dd)
    (twoChannel_nonExplosive hdd)
    (twoChannel_conditionalHoldingTimeLaw hlam hp0 hp1 t₀)
    (twoChannel_conditionalChannelLaw hlam hp0 hp1 t₀)
    (ageCounter_hazardContinuousAlongFlow _ _ (twoWeights_sum p)
      (continuous_rampRate lam (dd : ℝ)))
    (ageCounter_resetOccupationContinuousAlongFlow _ _ (twoWeights_sum p)
      (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)) hfc
      (twoShifts_continuous (dd : ℝ)))
    (ageCounter_resetOccupationRegular _ _ (twoWeights_sum p) (twoShifts_vanish hlam)
      (continuous_rampRate lam (dd : ℝ)).measurable (continuous_rampRate lam (dd : ℝ))
      hfm hfc (twoShifts_measurable (dd : ℝ)) (twoShifts_continuous (dd : ℝ)))
    (measurable_counterTestFunction hfm) C
    (fun z => abs_counterTestFunction_le hC z)
    (ageCounter_expectedResetIncrement_continuous _ _ (twoWeights_sum p)
      (twoShifts_vanish hlam) hfc (twoShifts_continuous (dd : ℝ)))
    lam (ageCounter_totalIntensity_le _ _ (twoWeights_sum p) (rampRate_le hlam.le _))
    (Lh * 1) (by simpa using hLh0)
    (ageCounter_expectedResetIncrement_lipschitz _ _ (twoWeights_sum p)
      (twoShifts_vanish hlam) hLh0 hL (twoShifts_lipschitz (dd : ℝ)))
    dd hdd (le_twoChannelNoise_holdingTime lam dd)
    (ageCounter_flowIntegralIdentity _ _) t

set_option maxHeartbeats 1000000 in
include hlam hdd hp0 hp1 in
/-- **The martingale property on the two-channel refractory clock**, for a
bounded Lipschitz profile of the counter. -/
theorem twoChannel_martingale_of_profile (hfm : Measurable hfun)
    (hfc : Continuous hfun) (hC : ∀ y, |hfun y| ≤ C) (hLh0 : 0 ≤ Lh)
    (hL : ∀ y y' : ℝ, |hfun y - hfun y'| ≤ Lh * |y - y'|) (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (fun _ => 0) (counterTestFunction hfun))
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
  exact martingale_davisElapsedCompensatedGeneratorProcess_markedJump_of_boundedIntensity
    (twoChannel_nonExplosive hdd)
    (twoChannel_conditionalHoldingTimeLaw hlam hp0 hp1 t₀)
    (twoChannel_conditionalChannelLaw hlam hp0 hp1 t₀)
    (ageCounter_hazardContinuousAlongFlow _ _ (twoWeights_sum p)
      (continuous_rampRate lam (dd : ℝ)))
    (ageCounter_resetOccupationContinuousAlongFlow _ _ (twoWeights_sum p)
      (twoShifts_vanish hlam) (continuous_rampRate lam (dd : ℝ)) hfc
      (twoShifts_continuous (dd : ℝ)))
    (ageCounter_resetOccupationRegular _ _ (twoWeights_sum p) (twoShifts_vanish hlam)
      (continuous_rampRate lam (dd : ℝ)).measurable (continuous_rampRate lam (dd : ℝ))
      hfm hfc (twoShifts_measurable (dd : ℝ)) (twoShifts_continuous (dd : ℝ)))
    (measurable_counterTestFunction hfm) C
    (fun z => abs_counterTestFunction_le hC z)
    (ageCounter_expectedResetIncrement_continuous _ _ (twoWeights_sum p)
      (twoShifts_vanish hlam) hfc (twoShifts_continuous (dd : ℝ)))
    lam (ageCounter_totalIntensity_le _ _ (twoWeights_sum p) (rampRate_le hlam.le _))
    (Lh * 1) (by simpa using hLh0)
    (ageCounter_expectedResetIncrement_lipschitz _ _ (twoWeights_sum p)
      (twoShifts_vanish hlam) hLh0 hL (twoShifts_lipschitz (dd : ℝ)))
    dd hdd (le_twoChannelNoise_holdingTime lam dd)
    (ageCounter_flowIntegralIdentity _ _)

end Profile

include hlam hdd hp0 hp1 in
/-- **The Dynkin identity on the two-channel refractory clock.**  For the cosine
of the counter as test function, the occupation-compensated increment has zero
mean at every elapsed time. -/
theorem twoChannel_integral_davisElapsedCompensatedGeneratorProcess_eq_zero
    (t₀ : ℝ) (t : ℝ≥0) :
    ∫ om, davisElapsedCompensatedGeneratorProcess
      (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
      (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd) (twoChannelInitial t₀)
      (fun _ => 0) twoChannelTest t om ∂(twoChannelMeasure p hp0 hp1) = 0 :=
  twoChannel_dynkin_of_profile hlam hdd hp0 hp1 Real.continuous_cos.measurable
    Real.continuous_cos (fun y => Real.abs_cos_le_one y) zero_le_one cos_lipschitz t₀ t

include hlam hdd hp0 hp1 in
/-- **The martingale property on the two-channel refractory clock.**  The
occupation-compensated test-function process is a martingale for the
observation filtration of the marked jump history. -/
theorem twoChannel_martingale_davisElapsedCompensatedGeneratorProcess (t₀ : ℝ) :
    Martingale
      (davisElapsedCompensatedGeneratorProcess
        (twoChannelModel lam hlam dd p hp0 hp1) (twoChannelFlow lam hlam dd p hp0 hp1)
        (twoChannelNoise lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀) (fun _ => 0) twoChannelTest)
      ((twoChannelNoise lam dd).markedJumpFiltration
        (twoChannelModel lam hlam dd p hp0 hp1)
        (twoChannelFlow lam hlam dd p hp0 hp1)
        (ageCounter_flowRegular _ _)
        (ageCounter_resetRegular _ _ (twoShifts_measurable _))
        (twoChannelNoise_measurable lam dd) (twoChannel_nonExplosive hdd)
        (twoChannelInitial t₀))
      (twoChannelMeasure p hp0 hp1) :=
  twoChannel_martingale_of_profile hlam hdd hp0 hp1 Real.continuous_cos.measurable
    Real.continuous_cos (fun y => Real.abs_cos_le_one y) zero_le_one cos_lipschitz t₀

end TwoChannel

end SHS
