import SHSLib.Core.DavisPoissonClockModel
import SHSLib.Core.DavisCoordinateNoise

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # A concrete noise satisfying the conditional laws

The constant-rate clock of `SHSLib.Core.DavisPoissonClockModel` has the
survivor factor `exp (-(lam * u))`, independently of the state and of the
history.  The matching noise is therefore a sequence of independent
exponentially distributed holding times, which is what this module builds: the
sample space is the path space `ℕ → ℝ`, the measure is the countable product of
exponential laws of rate `lam`, the `k`-th holding time is the (truncated)
`k`-th coordinate, and the single channel mark is constant.

The two conditional laws assumed throughout the development — the conditional
holding-time law and the conditional channel law — are *proved* here for this
noise, by the general criterion of `SHSLib.Core.DavisCoordinateNoise`.  This
supplies the first genuine instance of the hypotheses used by the Davis
one-segment results.
-/

namespace SHS

/-! ## The exponential tail -/

/-- The tail of the exponential law of rate `lam`. -/
theorem expMeasure_Ioi {lam : ℝ} (hlam : 0 < lam) {x : ℝ} (hx : 0 ≤ x) :
    expMeasure lam (Set.Ioi x) = ENNReal.ofReal (Real.exp (-(lam * x))) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  have h1 : expMeasure lam (Set.Iic x) = ENNReal.ofReal (1 - Real.exp (-(lam * x))) := by
    rw [← ofReal_cdf, cdf_expMeasure_eq hlam, if_pos hx]
  have h2 : Set.Ioi x = (Set.Iic x)ᶜ := by simp
  rw [h2, prob_compl_eq_one_sub measurableSet_Iic, h1]
  have he : Real.exp (-(lam * x)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hpos : (0 : ℝ) ≤ Real.exp (-(lam * x)) := (Real.exp_pos _).le
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
    ← ENNReal.ofReal_sub _ (by linarith)]
  ring_nf

/-! ## The product of exponential holding times -/

/-- The law of a sequence of independent exponential holding times of rate
`lam`, on the path space `ℕ → ℝ`. -/
def expPathMeasure (lam : ℝ) (hlam : 0 < lam) : Measure (ℕ → ℝ) :=
  @coordinatePathMeasure (expMeasure lam) (isProbabilityMeasure_expMeasure hlam)

instance isProbabilityMeasure_expPathMeasure (lam : ℝ) (hlam : 0 < lam) :
    IsProbabilityMeasure (expPathMeasure lam hlam) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [expPathMeasure]
  infer_instance

/-- The noise of the constant-rate clock: independent exponential holding
times, and the constant single mark. -/
abbrev poissonClockNoise : DavisJumpNoise 1 (ℕ → ℝ) := coordinateNoise Real.toNNReal

theorem poissonClockNoise_measurable : poissonClockNoise.MeasurableNoise :=
  coordinateNoise_measurable measurable_real_toNNReal

/-! ## The conditional laws hold for this noise -/

section Laws

variable (lam : ℝ) (hlam : 0 < lam)

/-- Abbreviation for the constant-rate clock at a positive rate. -/
abbrev poissonClockModel : SHS Bool 0 1 := poissonClockSHS lam hlam.le

/-- Abbreviation for its trivial flow. -/
abbrev poissonClockModelFlow : (poissonClockModel lam hlam).HasGlobalFlow :=
  poissonClockFlow lam hlam.le

/-- **Independence of the next holding time from the history.**  For an event
determined by the first `k` jumps, the probability of surviving an extra
duration `u` factorizes with the exponential survivor factor. -/
theorem poissonClock_measure_inter_holdingTime
    (initial : DavisState Bool 0) (k : ℕ) (u : ℝ≥0) (A : Set (ℕ → ℝ))
    (hA : MeasurableSet[poissonClockNoise.preJumpHistorySpace
      (poissonClockModel lam hlam) (poissonClockModelFlow lam hlam) initial k] A) :
    expPathMeasure lam hlam (A ∩ {ω | u < poissonClockNoise.holdingTime k ω})
      = expPathMeasure lam hlam A *
        ENNReal.ofReal (Real.exp (-(lam * (u : ℝ)))) := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [expPathMeasure, coordinateNoise_measure_inter_holdingTime
    (poissonClockModel lam hlam) (poissonClockModelFlow lam hlam)
    (poissonClock_flowRegular lam hlam.le) (poissonClock_resetRegular lam hlam.le)
    (expMeasure lam) measurable_real_toNNReal initial k u A hA]
  congr 1
  have hset : {x : ℝ | u < x.toNNReal} = Set.Ioi (u : ℝ) := by
    ext x
    simp [Real.lt_toNNReal_iff_coe_lt]
  rw [hset, expMeasure_Ioi hlam u.coe_nonneg]

/-- **The conditional holding-time law holds for the exponential noise.** -/
theorem poissonClock_conditionalHoldingTimeLaw (initial : DavisState Bool 0) :
    poissonClockNoise.ConditionalHoldingTimeLaw (poissonClockModel lam hlam)
      (poissonClockModelFlow lam hlam) (poissonClock_flowRegular lam hlam.le)
      (poissonClock_resetRegular lam hlam.le) (expPathMeasure lam hlam)
      poissonClockNoise_measurable initial := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [expPathMeasure]
  refine coordinateNoise_conditionalHoldingTimeLaw _ _ _ _ (expMeasure lam)
    measurable_real_toNNReal initial (fun u => Real.exp (-(lam * (u : ℝ)))) ?_ ?_
  · intro k ω u
    rw [DavisPreJumpHistory.nextSurvivor, poissonClock_segmentSurvivor]
  · intro u
    have hset : {x : ℝ | u < x.toNNReal} = Set.Ioi (u : ℝ) := by
      ext x
      simp [Real.lt_toNNReal_iff_coe_lt]
    rw [hset, expMeasure_Ioi hlam u.coe_nonneg]

/-- **The conditional channel law holds for the exponential noise.**  With a
single reset channel the normalized channel weight is one at every state of
positive intensity, and the constant mark realizes it. -/
theorem poissonClock_conditionalChannelLaw (initial : DavisState Bool 0) :
    poissonClockNoise.ConditionalChannelLaw (poissonClockModel lam hlam)
      (poissonClockModelFlow lam hlam) (expPathMeasure lam hlam) initial := by
  haveI := isProbabilityMeasure_expMeasure hlam
  rw [expPathMeasure]
  refine coordinateNoise_conditionalChannelLaw _ _ (expMeasure lam) Real.toNNReal
    initial ?_
  intro k
  filter_upwards with ω
  rw [davisChannelProbability, poissonClock_totalIntensity]
  simp [poissonClockSHS, div_self (ne_of_gt hlam)]

end Laws

end SHS
