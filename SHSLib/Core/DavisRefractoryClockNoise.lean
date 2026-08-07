import SHSLib.Core.DavisRefractoryClockModel
import SHSLib.Core.DavisPoissonClockNoise

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # A refractory instance with holding times bounded below

The refractory clock of `SHSLib.Core.DavisRefractoryClockModel` has, from an
age-zero state, the survivor factor `exp (-(lam * max (u - d) 0))`.  The
matching holding times are therefore `d` plus an exponential variable of rate
`lam`, and this module builds that noise on the path space: the `k`-th holding
time is `d` plus the truncated `k`-th coordinate, and the coordinates are
independent with the exponential law of rate `lam`.

Both conditional laws hold for this instance, and — unlike the constant-rate
clock — its holding times are bounded below by `d` *pointwise*, which is the
remaining hypothesis of the model-level martingale and Dynkin statements.  So
the refractory window identified in batch 125 is realized by a genuine object.
-/

namespace SHS

section Refractory

variable (lam : ℝ) (hlam : 0 < lam) (dd : ℝ≥0)

/-- The holding-time readout of the refractory clock: a fixed dead time `dd`
plus an exponential variable. -/
def refractoryHolding (dd : ℝ≥0) : ℝ → ℝ≥0 := fun x => dd + x.toNNReal

theorem measurable_refractoryHolding : Measurable (refractoryHolding dd) :=
  measurable_const.add measurable_real_toNNReal

/-- **The holding times of the refractory noise are bounded below by the dead
time**, for every sample. -/
theorem le_refractoryHolding (x : ℝ) : dd ≤ refractoryHolding dd x :=
  le_add_of_nonneg_right (zero_le _)

/-- The noise of the refractory clock. -/
abbrev refractoryNoise (dd : ℝ≥0) : DavisJumpNoise 1 (ℕ → ℝ) :=
  coordinateNoise (refractoryHolding dd)

theorem refractoryNoise_measurable : (refractoryNoise dd).MeasurableNoise :=
  coordinateNoise_measurable (measurable_refractoryHolding dd)

/-- Every holding time of the refractory noise is at least the dead time. -/
theorem le_refractoryNoise_holdingTime (k : ℕ) (ω : ℕ → ℝ) :
    dd ≤ (refractoryNoise dd).holdingTime k ω :=
  le_refractoryHolding dd (ω k)

include hlam in
/-- **The tail of a shifted exponential holding time** matches the survivor
factor of the refractory clock. -/
theorem expMeasure_refractoryHolding_gt (u : ℝ≥0) :
    expMeasure lam {x : ℝ | u < refractoryHolding dd x}
      = ENNReal.ofReal (Real.exp (-(lam * max ((u : ℝ) - (dd : ℝ)) 0))) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rcases lt_or_ge (u : ℝ) (dd : ℝ) with hu | hu
  · -- below the dead time the holding time always survives
    have hset : {x : ℝ | u < refractoryHolding dd x} = Set.univ := by
      ext x
      have : u < dd := by exact_mod_cast hu
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, refractoryHolding]
      exact lt_of_lt_of_le this (le_add_of_nonneg_right (zero_le _))
    rw [hset, measure_univ, max_eq_right (by linarith)]
    simp
  · -- above the dead time it is the exponential tail
    have hmax : max ((u : ℝ) - (dd : ℝ)) 0 = (u : ℝ) - (dd : ℝ) :=
      max_eq_left (by linarith)
    have hset : {x : ℝ | u < refractoryHolding dd x}
        = Set.Ioi ((u : ℝ) - (dd : ℝ)) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Ioi, refractoryHolding]
      constructor
      · intro h
        have h' : (u : ℝ) < (dd : ℝ) + max x 0 := by
          have := (NNReal.coe_lt_coe).2 h
          simpa [Real.coe_toNNReal'] using this
        rcases le_or_gt x 0 with hx | hx
        · simp only [max_eq_right hx, add_zero] at h'
          linarith
        · simp only [max_eq_left hx.le] at h'
          linarith
      · intro h
        have hx : 0 < x := lt_of_le_of_lt (by linarith) h
        have : (u : ℝ) < (dd : ℝ) + max x 0 := by
          simp only [max_eq_left hx.le]
          linarith
        have := (NNReal.coe_lt_coe (r₁ := u) (r₂ := dd + x.toNNReal))
        rw [← this]
        simpa [Real.coe_toNNReal'] using ‹(u : ℝ) < (dd : ℝ) + max x 0›
    rw [hset, expMeasure_Ioi hlam (by linarith : (0 : ℝ) ≤ (u : ℝ) - (dd : ℝ)), hmax]

/-- The refractory model at the dead time `dd`. -/
abbrev refractoryModel : SHS Bool 1 1 := refractoryClockSHS lam (dd : ℝ) hlam.le

/-- Its flow. -/
abbrev refractoryModelFlow : (refractoryModel lam hlam dd).HasGlobalFlow :=
  refractoryClockFlow lam (dd : ℝ) hlam.le

/-- The initial state used for the refractory instance: age zero at the clock
value `t₀`. -/
def refractoryInitial (t₀ : ℝ) : DavisState Bool 1 := (true, 0, t₀)

@[simp] theorem refractoryInitial_age (t₀ : ℝ) : (refractoryInitial t₀).2.1 0 = 0 := by
  simp [refractoryInitial]

/-- **The conditional holding-time law holds for the refractory instance.** -/
theorem refractory_conditionalHoldingTimeLaw (t₀ : ℝ) :
    (refractoryNoise dd).ConditionalHoldingTimeLaw (refractoryModel lam hlam dd)
      (refractoryModelFlow lam hlam dd)
      (refractoryClock_flowRegular lam (dd : ℝ) hlam.le)
      (refractoryClock_resetRegular lam (dd : ℝ) hlam.le)
      (expPathMeasure lam hlam)
      (refractoryNoise_measurable dd) (refractoryInitial t₀) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [expPathMeasure]
  refine coordinateNoise_conditionalHoldingTimeLaw _ _ _ _ (expMeasure lam)
    (measurable_refractoryHolding dd) (refractoryInitial t₀)
    (fun u => Real.exp (-(lam * max ((u : ℝ) - (dd : ℝ)) 0))) ?_ ?_
  · intro k ω u
    refine refractoryClock_segmentSurvivor lam (dd : ℝ) hlam.le dd.coe_nonneg _ ?_ u
    exact refractoryClock_stateAfterJump_age lam (dd : ℝ) hlam.le _ _
      (refractoryInitial_age t₀) _ ω
  · intro u
    exact expMeasure_refractoryHolding_gt lam hlam dd u

/-- **The conditional channel law holds for the refractory instance.**  The
state reached just before a jump has age at least the dead time, so the single
channel is active there and its normalized weight is one. -/
theorem refractory_conditionalChannelLaw (t₀ : ℝ) :
    (refractoryNoise dd).ConditionalChannelLaw (refractoryModel lam hlam dd)
      (refractoryModelFlow lam hlam dd) (expPathMeasure lam hlam)
      (refractoryInitial t₀) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [expPathMeasure]
  refine coordinateNoise_conditionalChannelLaw _ _ (expMeasure lam)
    (refractoryHolding dd) (refractoryInitial t₀) ?_
  intro k
  filter_upwards with ω
  have hage : ((davisPreJumpHistory (refractoryModel lam hlam dd)
      (refractoryModelFlow lam hlam dd) (refractoryNoise dd) (refractoryInitial t₀)
        k ω).stateBeforeNextJump (refractoryModel lam hlam dd)
          (refractoryModelFlow lam hlam dd)
          ((refractoryNoise dd).holdingTime k ω)).2.1 0
      = ((refractoryNoise dd).holdingTime k ω : ℝ) := by
    rw [DavisPreJumpHistory.stateBeforeNextJump,
      refractoryClock_davisFlow_age lam (dd : ℝ) hlam.le]
    rw [show (davisPreJumpHistory (refractoryModel lam hlam dd)
      (refractoryModelFlow lam hlam dd) (refractoryNoise dd)
        (refractoryInitial t₀) k ω).currentState.2.1 0 = 0 from
      refractoryClock_stateAfterJump_age lam (dd : ℝ) hlam.le _ _
        (refractoryInitial_age t₀) _ ω]
    ring
  have hactive : (dd : ℝ) ≤ ((davisPreJumpHistory (refractoryModel lam hlam dd)
      (refractoryModelFlow lam hlam dd) (refractoryNoise dd) (refractoryInitial t₀)
        k ω).stateBeforeNextJump (refractoryModel lam hlam dd)
          (refractoryModelFlow lam hlam dd)
          ((refractoryNoise dd).holdingTime k ω)).2.1 0 := by
    rw [hage]
    exact_mod_cast le_refractoryNoise_holdingTime dd k ω
  rw [davisChannelProbability, refractoryClock_totalIntensity, if_pos hactive]
  show (if (dd : ℝ) ≤ ((davisPreJumpHistory (refractoryModel lam hlam dd)
      (refractoryModelFlow lam hlam dd) (refractoryNoise dd) (refractoryInitial t₀)
        k ω).stateBeforeNextJump (refractoryModel lam hlam dd)
          (refractoryModelFlow lam hlam dd)
          ((refractoryNoise dd).holdingTime k ω)).2.1 0 then lam else 0) / lam = 1
  rw [if_pos hactive, div_self (ne_of_gt hlam)]

end Refractory

end SHS
