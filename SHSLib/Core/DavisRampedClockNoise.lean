import SHSLib.Core.DavisRampedClockModel
import SHSLib.Core.DavisRefractoryClockNoise

open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-! # The noise of the ramped refractory clock

The ramped clock of `SHSLib.Core.DavisRampedClockModel` has, from an age-zero
state, the survivor factor `exp (-Λ u)` with

`Λ u = lam · (max (u - d) 0 ^ 2 / 2 − max (u - (d+1)) 0 ^ 2 / 2)`.

Its holding times are therefore no longer a shifted exponential, and the
matching law has to be produced by hand.  The device used here is the classical
inverse-transform: `Λ` is a continuous increasing bijection from the ages above
`d` onto the nonnegative reals, with explicit inverse

`Λ⁻¹ y = d + (if y ≤ lam / 2 then √(2y/lam) else 1/2 + y/lam)`,

so applying `Λ⁻¹` to a *unit exponential* variable produces exactly the holding
time we need: `P (Λ⁻¹ E > u) = P (E > Λ u) = exp (-Λ u)`.  The holding times so
obtained are at least `d` for every sample, which is the refractory window the
model-level martingale statements require.

Both conditional laws are proved here, by the general criterion of
`SHSLib.Core.DavisCoordinateNoise`.
-/

namespace SHS

section Ramped

variable {lam : ℝ} (hlam : 0 < lam)

/-- The elapsed age past the dead time, as a function of a unit exponential
sample: the inverse of the accumulated ramped hazard. -/
def rampedHoldingProfile (lam : ℝ) (x : ℝ) : ℝ :=
  if x ≤ lam / 2 then Real.sqrt (2 * x / lam) else 1 / 2 + x / lam

/-- The holding-time readout of the ramped clock: the dead time `dd` plus the
inverse hazard applied to the sample. -/
def rampedHolding (lam : ℝ) (dd : ℝ≥0) : ℝ → ℝ≥0 := fun x =>
  dd + (rampedHoldingProfile lam x).toNNReal

theorem measurable_rampedHoldingProfile (lam : ℝ) :
    Measurable (rampedHoldingProfile lam) := by
  unfold rampedHoldingProfile
  refine Measurable.ite (measurableSet_le measurable_id measurable_const) ?_ ?_
  · exact Real.continuous_sqrt.measurable.comp (by fun_prop)
  · fun_prop

theorem measurable_rampedHolding (lam : ℝ) (dd : ℝ≥0) :
    Measurable (rampedHolding lam dd) :=
  measurable_const.add ((measurable_rampedHoldingProfile lam).real_toNNReal)

/-- **The holding times of the ramped noise are bounded below by the dead
time**, for every sample. -/
theorem le_rampedHolding (lam : ℝ) (dd : ℝ≥0) (x : ℝ) : dd ≤ rampedHolding lam dd x :=
  le_add_of_nonneg_right (zero_le _)

include hlam in
theorem rampedHoldingProfile_pos {x : ℝ} (hx : 0 < x) : 0 < rampedHoldingProfile lam x := by
  rw [rampedHoldingProfile]
  split
  · exact Real.sqrt_pos.2 (by positivity)
  · positivity

include hlam in
/-- **The inverse-transform identity.**  For a positive sample, the holding time
exceeds the elapsed age `u` exactly when the sample exceeds the hazard
accumulated up to `u`. -/
theorem rampedHolding_gt_iff (dd : ℝ≥0) (u : ℝ≥0) {x : ℝ} (hx : 0 < x) :
    u < rampedHolding lam dd x ↔ rampedHazard lam (dd : ℝ) (u : ℝ) < x := by
  have hD : (0 : ℝ) ≤ (dd : ℝ) := dd.coe_nonneg
  have hP : 0 < rampedHoldingProfile lam x := rampedHoldingProfile_pos hlam hx
  have hcoe : ((rampedHolding lam dd x : ℝ≥0) : ℝ)
      = (dd : ℝ) + rampedHoldingProfile lam x := by
    rw [rampedHolding]
    push_cast
    rw [Real.coe_toNNReal _ hP.le]
  have hstep : u < rampedHolding lam dd x ↔
      (u : ℝ) < (dd : ℝ) + rampedHoldingProfile lam x := by
    rw [← NNReal.coe_lt_coe, hcoe]
  rw [hstep]
  set v : ℝ := (u : ℝ) - (dd : ℝ) with hv
  rcases lt_or_ge v 0 with hv0 | hv0
  · -- below the dead time: both sides hold
    have hL : (u : ℝ) < (dd : ℝ) + rampedHoldingProfile lam x := by
      simp only [hv, sub_neg] at hv0
      linarith
    have hR : rampedHazard lam (dd : ℝ) (u : ℝ) < x := by
      rw [rampedHazard_zero_of_le (by simp only [hv, sub_neg] at hv0; linarith)]
      exact hx
    simp [hL, hR]
  · -- above the dead time
    have hu1 : (u : ℝ) = (dd : ℝ) + v := by rw [hv]; ring
    have hmax1 : max ((u : ℝ) - (dd : ℝ)) 0 = v := max_eq_left hv0
    have hlt : (u : ℝ) < (dd : ℝ) + rampedHoldingProfile lam x ↔
        v < rampedHoldingProfile lam x := by
      rw [hu1]; constructor <;> intro h <;> linarith
    rw [hlt]
    rcases le_total v 1 with hv1 | hv1
    · -- the quadratic branch of the hazard
      have hhaz : rampedHazard lam (dd : ℝ) (u : ℝ) = lam * v ^ 2 / 2 := by
        rw [rampedHazard, hmax1,
          max_eq_right (by rw [hu1]; linarith : (u : ℝ) - ((dd : ℝ) + 1) ≤ 0)]
        ring
      rw [hhaz, rampedHoldingProfile]
      by_cases hx2 : x ≤ lam / 2
      · rw [if_pos hx2, Real.lt_sqrt hv0]
        constructor
        · intro h
          rw [lt_div_iff₀ hlam] at h
          linarith
        · intro h
          rw [lt_div_iff₀ hlam]
          linarith
      · rw [if_neg hx2]
        push_neg at hx2
        have hL : v < 1 / 2 + x / lam := by
          have hhalf : 1 / 2 < x / lam := by
            rw [lt_div_iff₀ hlam]
            linarith
          linarith
        have hv2 : v ^ 2 ≤ 1 := by nlinarith
        have hR : lam * v ^ 2 / 2 < x := by nlinarith
        exact iff_of_true hL hR
    · -- the linear branch of the hazard
      have hhaz : rampedHazard lam (dd : ℝ) (u : ℝ) = lam * (v - 1 / 2) := by
        rw [rampedHazard, hmax1,
          max_eq_left (by rw [hu1]; linarith : (0 : ℝ) ≤ (u : ℝ) - ((dd : ℝ) + 1))]
        rw [hu1]
        ring
      rw [hhaz, rampedHoldingProfile]
      by_cases hx2 : x ≤ lam / 2
      · rw [if_pos hx2]
        have hsq : Real.sqrt (2 * x / lam) ≤ 1 := by
          rw [Real.sqrt_le_one, div_le_one hlam]
          linarith
        have hL : ¬ (v < Real.sqrt (2 * x / lam)) := by
          push_neg
          linarith
        have hR : ¬ (lam * (v - 1 / 2) < x) := by
          push_neg
          nlinarith
        exact iff_of_false hL hR
      · rw [if_neg hx2]
        push_neg at hx2
        have hxl : x / lam * lam = x := div_mul_cancel₀ _ (ne_of_gt hlam)
        constructor
        · intro h
          have h1 : v - 1 / 2 < x / lam := by linarith
          have h2 : (v - 1 / 2) * lam < x / lam * lam :=
            mul_lt_mul_of_pos_right h1 hlam
          rw [hxl] at h2
          nlinarith
        · intro h
          have h2 : v - 1 / 2 < x / lam := by
            rw [lt_div_iff₀ hlam]
            nlinarith
          linarith

/-! ## The tail of a unit exponential sample -/

theorem expMeasure_one_Iic_zero : expMeasure 1 (Set.Iic (0 : ℝ)) = 0 := by
  haveI := isProbabilityMeasure_expMeasure (one_pos : (0 : ℝ) < 1)
  have h1 : expMeasure 1 (Set.Ioi (0 : ℝ)) = 1 := by
    rw [expMeasure_Ioi one_pos le_rfl]
    simp
  have h2 := measure_add_measure_compl (μ := expMeasure 1)
    (measurableSet_Iic (a := (0 : ℝ)))
  rw [show (Set.Iic (0 : ℝ))ᶜ = Set.Ioi 0 by simp, h1, measure_univ] at h2
  simpa using h2

include hlam in
/-- **The tail of the ramped holding time** matches the survivor factor of the
ramped clock. -/
theorem expMeasure_one_rampedHolding_gt (dd : ℝ≥0) (u : ℝ≥0) :
    expMeasure 1 {x : ℝ | u < rampedHolding lam dd x}
      = ENNReal.ofReal (Real.exp (-rampedHazard lam (dd : ℝ) (u : ℝ))) := by
  haveI := isProbabilityMeasure_expMeasure (one_pos : (0 : ℝ) < 1)
  set L : ℝ := rampedHazard lam (dd : ℝ) (u : ℝ) with hL
  have hL0 : 0 ≤ L := rampedHazard_nonneg hlam.le _ _
  have hae : {x : ℝ | u < rampedHolding lam dd x} =ᵐ[expMeasure 1] Set.Ioi L := by
    refine MeasureTheory.ae_eq_set.2 ⟨?_, ?_⟩
    · refine measure_mono_null ?_ expMeasure_one_Iic_zero
      intro x hx
      by_contra hpos
      simp only [Set.mem_Iic, not_le] at hpos
      exact hx.2 ((rampedHolding_gt_iff hlam dd u hpos).1 hx.1)
    · refine measure_mono_null ?_ expMeasure_one_Iic_zero
      intro x hx
      by_contra hpos
      simp only [Set.mem_Iic, not_le] at hpos
      exact hx.2 ((rampedHolding_gt_iff hlam dd u hpos).2 hx.1)
  rw [measure_congr hae, expMeasure_Ioi one_pos hL0, one_mul]

/-! ## The instance -/

/-- The noise of the ramped clock. -/
abbrev rampedNoise (lam : ℝ) (dd : ℝ≥0) : DavisJumpNoise 1 (ℕ → ℝ) :=
  coordinateNoise (rampedHolding lam dd)

theorem rampedNoise_measurable (lam : ℝ) (dd : ℝ≥0) :
    (rampedNoise lam dd).MeasurableNoise :=
  coordinateNoise_measurable (measurable_rampedHolding lam dd)

/-- Every holding time of the ramped noise is at least the dead time. -/
theorem le_rampedNoise_holdingTime (lam : ℝ) (dd : ℝ≥0) (k : ℕ) (ω : ℕ → ℝ) :
    dd ≤ (rampedNoise lam dd).holdingTime k ω :=
  le_rampedHolding lam dd (ω k)

/-- The ramped model at the dead time `dd`. -/
abbrev rampedModel (lam : ℝ) (hlam : 0 < lam) (dd : ℝ≥0) : SHS Bool 1 1 :=
  rampedClockSHS lam (dd : ℝ) hlam.le

/-- Its flow. -/
abbrev rampedModelFlow (lam : ℝ) (hlam : 0 < lam) (dd : ℝ≥0) :
    (rampedModel lam hlam dd).HasGlobalFlow :=
  rampedClockFlow lam (dd : ℝ) hlam.le

/-- The initial state: age zero at the clock value `t₀`. -/
def rampedInitial (t₀ : ℝ) : DavisState Bool 1 := (true, 0, t₀)

@[simp] theorem rampedInitial_age (t₀ : ℝ) : (rampedInitial t₀).2.1 0 = 0 := by
  simp [rampedInitial]

/-- The law of the ramped instance: independent unit exponential samples. -/
abbrev unitExpPathMeasure : Measure (ℕ → ℝ) := expPathMeasure 1 one_pos

include hlam in
/-- **The conditional holding-time law holds for the ramped instance.** -/
theorem ramped_conditionalHoldingTimeLaw (dd : ℝ≥0) (t₀ : ℝ) :
    (rampedNoise lam dd).ConditionalHoldingTimeLaw (rampedModel lam hlam dd)
      (rampedModelFlow lam hlam dd)
      (ageClock_flowRegular (rampRate lam (dd : ℝ)) (rampRate_nonneg hlam.le (dd : ℝ)))
      (ageClock_resetRegular (rampRate lam (dd : ℝ)) (rampRate_nonneg hlam.le (dd : ℝ)))
      unitExpPathMeasure (rampedNoise_measurable lam dd) (rampedInitial t₀) := by
  haveI := isProbabilityMeasure_expMeasure (one_pos : (0 : ℝ) < 1)
  rw [unitExpPathMeasure, expPathMeasure]
  refine coordinateNoise_conditionalHoldingTimeLaw _ _ _ _ (expMeasure 1)
    (measurable_rampedHolding lam dd) (rampedInitial t₀)
    (fun u => Real.exp (-rampedHazard lam (dd : ℝ) (u : ℝ))) ?_ ?_
  · intro k ω u
    refine rampedClock_segmentSurvivor hlam.le dd.coe_nonneg _ ?_ u
    exact ageClock_stateAfterJump_age _ _ _ _ (rampedInitial_age t₀) _ ω
  · intro u
    exact expMeasure_one_rampedHolding_gt hlam dd u

include hlam in
/-- **The conditional channel law holds for the ramped instance.**  Almost
surely the sample is positive, so the age reached just before a jump is
strictly beyond the dead time, where the single channel is active. -/
theorem ramped_conditionalChannelLaw (dd : ℝ≥0) (t₀ : ℝ) :
    (rampedNoise lam dd).ConditionalChannelLaw (rampedModel lam hlam dd)
      (rampedModelFlow lam hlam dd) unitExpPathMeasure (rampedInitial t₀) := by
  haveI := isProbabilityMeasure_expMeasure (one_pos : (0 : ℝ) < 1)
  rw [unitExpPathMeasure, expPathMeasure]
  refine coordinateNoise_conditionalChannelLaw _ _ (expMeasure 1)
    (rampedHolding lam dd) (rampedInitial t₀) ?_
  intro k
  have hpos : ∀ᵐ ω ∂(coordinatePathMeasure (expMeasure 1)), 0 < ω k := by
    have hnull : coordinatePathMeasure (expMeasure 1) {ω : ℕ → ℝ | ω k ∈ Set.Iic (0 : ℝ)}
        = 0 := by
      rw [coordinatePathMeasure_coordinate (expMeasure 1) k measurableSet_Iic]
      exact expMeasure_one_Iic_zero
    rw [ae_iff]
    refine measure_mono_null ?_ hnull
    intro ω hω
    simpa using le_of_not_gt hω
  filter_upwards [hpos] with ω hω
  set z := (davisPreJumpHistory (rampedModel lam hlam dd) (rampedModelFlow lam hlam dd)
    (rampedNoise lam dd) (rampedInitial t₀) k ω).stateBeforeNextJump
      (rampedModel lam hlam dd) (rampedModelFlow lam hlam dd)
      ((rampedNoise lam dd).holdingTime k ω) with hz
  have hage : z.2.1 0 = ((rampedNoise lam dd).holdingTime k ω : ℝ) := by
    rw [hz, DavisPreJumpHistory.stateBeforeNextJump]
    rw [show (davisFlow (rampedModel lam hlam dd) (rampedModelFlow lam hlam dd)
        ((rampedNoise lam dd).holdingTime k ω)
        (davisPreJumpHistory (rampedModel lam hlam dd) (rampedModelFlow lam hlam dd)
          (rampedNoise lam dd) (rampedInitial t₀) k ω).currentState).2.1 0
      = (davisPreJumpHistory (rampedModel lam hlam dd) (rampedModelFlow lam hlam dd)
          (rampedNoise lam dd) (rampedInitial t₀) k ω).currentState.2.1 0
        + ((rampedNoise lam dd).holdingTime k ω : ℝ) from
      ageClock_davisFlow_age _ _ _ _]
    rw [show (davisPreJumpHistory (rampedModel lam hlam dd) (rampedModelFlow lam hlam dd)
        (rampedNoise lam dd) (rampedInitial t₀) k ω).currentState.2.1 0 = 0 from
      ageClock_stateAfterJump_age _ _ _ _ (rampedInitial_age t₀) _ ω]
    ring
  have hgt : (dd : ℝ) < z.2.1 0 := by
    rw [hage, show (rampedNoise lam dd).holdingTime k ω = rampedHolding lam dd (ω k)
      from rfl, rampedHolding]
    push_cast
    have := rampedHoldingProfile_pos hlam hω
    rw [Real.coe_toNNReal _ this.le]
    linarith
  have hrate : rampRate lam (dd : ℝ) (z.2.1 0) ≠ 0 := by
    intro h
    exact absurd ((rampRate_eq_zero_iff hlam (dd : ℝ) (z.2.1 0)).1 h) (not_le.2 hgt)
  rw [davisChannelProbability]
  show rampRate lam (dd : ℝ) (z.2.1 0) / (rampedModel lam hlam dd).totalIntensity z = 1
  rw [show (rampedModel lam hlam dd).totalIntensity z = rampRate lam (dd : ℝ) (z.2.1 0) from
    ageClock_totalIntensity _ _ z, div_self hrate]

end Ramped

end SHS
