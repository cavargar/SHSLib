import SHSLib.Core.DavisMarkedJumpSegmentMartingale
import SHSLib.Core.DavisProfileLinearGrowth

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The conditional step law under a horizon-dependent profile bound

Every consumer of the bound on the centered reset profile now carries an age
horizon, but the conditional step law of the marked jump filtration still asks
for a bound valid at *every* age.  That bound was shown to be unavailable: a
uniformly bounded accumulated hazard is incompatible with the conditional
holding-time law, and what a bounded intensity gives instead is a bound that
grows linearly in the age.

The fields of `DavisSegmentConditionalStepLaw` are, however, quantified over
the observation times, and every age that enters the field at time `t` is at
most `t`.  So the constant `K` may be replaced by a function `Kf : ℝ≥0 → ℝ` of
the observation time, subject to

`∀ t z r, r ≤ t → |Φ(z, r)| ≤ Kf t`.

This module carries out that replacement, for the conditional step law of the
marked jump filtration and for its two consequences — the one-segment
martingale and the deterministic-cap increment law — and then instantiates it
at the linear growth bound, which yields all three statements under a bounded
test function and a bounded intensity alone: no hypothesis on the accumulated
hazard, and no global bound on the profile.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## A pointwise compensator bound -/

/-- A bound on the centered reset profile *at one age* bounds the partial
occupation compensator at that age.  This is the pointwise refinement of
`abs_davisSegmentResetOccupationCompensator_le_of_profile`. -/
theorem abs_davisSegmentResetOccupationCompensator_le_of_profile_at
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg) (K : ℝ)
    (z : DavisState Q n) (u : ℝ≥0)
    (hK : |davisSegmentCenteredResetProfile S hflow g z ((u : ℝ≥0) : ℝ)| ≤ K) :
    |davisSegmentResetOccupationCompensator S hflow g z u| ≤ K + 2 * Cg := by
  rw [davisSegmentCenteredResetProfile, Real.toNNReal_coe] at hK
  have hE := abs_davisExpectedResetIncrement_le_all S g
    (davisFlow S hflow u z) Cg hgC
  have htri := abs_sub (davisExpectedResetIncrement S g (davisFlow S hflow u z))
    (davisExpectedResetIncrement S g (davisFlow S hflow u z) -
      davisSegmentResetOccupationCompensator S hflow g z u)
  have h0 : davisExpectedResetIncrement S g (davisFlow S hflow u z) -
      (davisExpectedResetIncrement S g (davisFlow S hflow u z) -
        davisSegmentResetOccupationCompensator S hflow g z u) =
      davisSegmentResetOccupationCompensator S hflow g z u := by ring
  rw [h0] at htri
  linarith

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The holding time of a segment completed before an elapsed time is at most
that time. -/
theorem DavisJumpNoise.holdingTime_le_of_jumpTime_succ_le {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (N : ℕ) (t : ℝ≥0) (ω : Ω)
    (h : ξ.jumpTime (N + 1) ω ≤ t) : ξ.holdingTime N ω ≤ t :=
  le_trans (by rw [ξ.jumpTime_succ]; exact le_add_self) h

/-! ## The conditional step law under a horizon-dependent bound -/

set_option maxHeartbeats 1000000 in
/-- **The conditional step law of the one-segment martingale for the marked
jump filtration, under a bound on the centered reset profile that is required
only below the observation time.** -/
theorem davisSegmentConditionalStepLaw_markedJump_horizon
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise} (hne : ξ.NonExplosive)
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hchan : ξ.ConditionalChannelLaw S hflow P initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (hreg : DavisResetOccupationRegular S hflow g)
    (hg : Measurable g) (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentCenteredResetProfile S hflow g p.1 p.2)
    (hPhicont : ∀ z,
      Continuous (davisSegmentCenteredResetProfile S hflow g z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |davisSegmentCenteredResetProfile S hflow g z r -
      davisSegmentCenteredResetProfile S hflow g z r'| ≤ L * |r - r'|)
    (Kf : ℝ≥0 → ℝ) (hKf : ∀ (t : ℝ≥0) (z : DavisState Q n) (r : ℝ),
      r ≤ (t : ℝ) → |davisSegmentCenteredResetProfile S hflow g z r| ≤ Kf t)
    (N : ℕ) :
    DavisSegmentConditionalStepLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g
      N := by
  classical
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC initial)
  have hKf0 : ∀ t : ℝ≥0, 0 ≤ Kf t := fun t =>
    le_trans (abs_nonneg _) (hKf t initial 0 t.coe_nonneg)
  -- the compensator is bounded at every age below the observation time
  have hcompbound : ∀ (t : ℝ≥0) (z : DavisState Q n) (u : ℝ≥0), u ≤ t →
      |davisSegmentResetOccupationCompensator S hflow g z u| ≤ Kf t + 2 * Cg :=
    fun t z u hu =>
      abs_davisSegmentResetOccupationCompensator_le_of_profile_at S hflow g Cg
        hgC (Kf t) z u (hKf t z _ (by exact_mod_cast hu))
  have hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2 := hreg.survivor_measurable
  -- a bounded measurable function is integrable over a finite measure
  have hboundint : ∀ (f : Ω → ℝ), Measurable f → ∀ (c : ℝ),
      (∀ ω, |f ω| ≤ c) → Integrable f P := by
    intro f hfm c hfc
    refine (integrable_const (max c 0)).mono' hfm.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact le_trans (hfc ω) (le_max_left c 0)
  have hcompletedm : ∀ t, Measurable
      (davisSegmentCompletedPart S hflow ξ initial g N t) := fun t =>
    hξ.measurable_segmentCompletedPart S hflow hf hr initial hg hreg N t
  have hactivem : ∀ t, Measurable
      (davisSegmentActivePart S hflow ξ initial g N t) := fun t =>
    hξ.measurable_segmentActivePart S hflow hf hr initial hreg N t
  have hcompletedb : ∀ (t : ℝ≥0) (ω : Ω),
      |davisSegmentCompletedPart S hflow ξ initial g N t ω| ≤
        2 * Cg + (Kf t + 2 * Cg) := by
    intro t ω
    have hKt := hKf0 t
    unfold davisSegmentCompletedPart davisSegmentCompletedContribution
    by_cases hend : ξ.jumpTime (N + 1) ω ≤ t
    · rw [if_pos hend]
      calc |davisRealizedResetIncrement S hflow ξ initial g N ω -
              davisSampledResetOccupationCompensator S hflow g ξ initial N ω|
          ≤ |davisRealizedResetIncrement S hflow ξ initial g N ω| +
            |davisSampledResetOccupationCompensator S hflow g ξ initial N ω| :=
            abs_sub _ _
        _ ≤ 2 * Cg + (Kf t + 2 * Cg) :=
            add_le_add (abs_davisRealizedResetIncrement_le S hflow ξ initial g
              Cg hgC N ω)
              (hcompbound t _ _ (ξ.holdingTime_le_of_jumpTime_succ_le N t ω hend))
    · rw [if_neg hend, abs_zero]
      positivity
  have hactiveb : ∀ (t : ℝ≥0) (ω : Ω),
      |davisSegmentActivePart S hflow ξ initial g N t ω| ≤ Kf t + 2 * Cg := by
    intro t ω
    have hKt := hKf0 t
    unfold davisSegmentActivePart
    by_cases hend : ξ.jumpTime (N + 1) ω ≤ t
    · rw [if_pos hend, abs_zero]; positivity
    · rw [if_neg hend]
      by_cases hstart : ξ.jumpTime N ω ≤ t
      · rw [if_pos hstart]; exact hcompbound t _ _ tsub_le_self
      · rw [if_neg hstart, abs_zero]; positivity
  -- the conditional active mean
  have hmeanm : ∀ s t : ℝ≥0, Measurable fun ω =>
      davisSegmentConditionalActiveMean S hflow g
        (davisStateAfterJump S hflow ξ initial N ω)
        (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω) := by
    intro s t
    have hz : Measurable (davisStateAfterJump S hflow ξ initial N) :=
      hξ.stateAfterJump S hflow hf hr initial N
    unfold davisSegmentConditionalActiveMean
    exact (((hsurv.comp (hz.prodMk (measurable_const.sub (hξ.jumpTime N)))).inv).mul
      (hsurv.comp (hz.prodMk (measurable_const.sub (hξ.jumpTime N))))).mul
      (hreg.stoppedCompensator_measurable.comp
        (hz.prodMk (measurable_const.sub (hξ.jumpTime N))))
  have hmeanb : ∀ (s t : ℝ≥0), s ≤ t → ∀ ω,
      |davisSegmentConditionalActiveMean S hflow g
        (davisStateAfterJump S hflow ξ initial N ω)
        (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω)| ≤ Kf t + 2 * Cg := by
    intro s t hst ω
    set z := davisStateAfterJump S hflow ξ initial N ω with hz
    set u := s - ξ.jumpTime N ω with hu
    set v := t - ξ.jumpTime N ω with hv
    have huv : u ≤ v := tsub_le_tsub_right hst _
    have hsu : 0 < davisSegmentSurvivor S hflow z u :=
      davisSegmentSurvivor_pos S hflow z u
    have hsv : 0 < davisSegmentSurvivor S hflow z v :=
      davisSegmentSurvivor_pos S hflow z v
    have hle : davisSegmentSurvivor S hflow z v ≤
        davisSegmentSurvivor S hflow z u :=
      davisSegmentSurvivor_antitone S hflow hcont z huv
    unfold davisSegmentConditionalActiveMean
    have hratio : (davisSegmentSurvivor S hflow z u)⁻¹ *
        davisSegmentSurvivor S hflow z v ≤ 1 := by
      rw [inv_mul_le_iff₀ hsu]
      simpa using hle
    have hratio0 : 0 ≤ (davisSegmentSurvivor S hflow z u)⁻¹ *
        davisSegmentSurvivor S hflow z v :=
      le_of_lt (mul_pos (inv_pos.2 hsu) hsv)
    rw [abs_mul, abs_of_nonneg hratio0]
    calc ((davisSegmentSurvivor S hflow z u)⁻¹ *
            davisSegmentSurvivor S hflow z v) *
          |davisSegmentResetOccupationCompensator S hflow g z v|
        ≤ 1 * (Kf t + 2 * Cg) :=
          mul_le_mul hratio (hcompbound t z v tsub_le_self) (abs_nonneg _)
            zero_le_one
      _ = Kf t + 2 * Cg := one_mul _
  refine
    { adapted := fun t => ?_
      jumpTime_observable := fun k t => ?_
      integrable_completedPart := fun t => ?_
      integrable_activePart := fun t => ?_
      integrableOn_conditionalActiveMean := fun s t hst => ?_
      completed_conditional := fun s t hst A hA hAsub => ?_
      active_conditional := fun s t hst A hA hAsub => ?_
      fresh_centered := fun s t _ A hA hAsub => ?_ }
  · exact (ξ.measurable_markedJump_segmentContribution S hflow hf hr hξ hne
      initial hg hreg N t).stronglyMeasurable
  · exact ξ.measurableSet_markedJump_jumpTime_le S hflow hf hr hξ initial k t
  · exact hboundint _ (hcompletedm t) _ (hcompletedb t)
  · exact hboundint _ (hactivem t) _ (hactiveb t)
  · exact (hboundint _ (hmeanm s t) _ (hmeanb s t hst)).integrableOn
  · exact DavisJumpNoise.markedJump_completed_conditional hlaw hchan hcont hsurv
      hg Cg hgC hPhimeas hPhicont L hL hlip ((t : ℝ≥0) : ℝ) (Kf t)
      (fun z r hr => hKf t z r hr) N s t hst le_rfl A hA hAsub
  · exact hlaw.markedJump_active_conditional hcont hreg N s t hst (Kf t + 2 * Cg)
      (fun ω => hcompbound t _ _ tsub_le_self) A hA hAsub
  · exact DavisJumpNoise.markedJump_fresh_centered hne hlaw hchan hcont hgcont
      hreg hg Cg hgC hPhimeas hPhicont L hL hlip ((t : ℝ≥0) : ℝ) (Kf t)
      (fun z r hr => hKf t z r hr) N s t le_rfl A hA hAsub

/-! ## Consequences under a horizon-dependent bound -/

/-- **The one-segment martingale for the marked jump filtration** under a
profile bound required only below the observation time. -/
theorem martingale_davisElapsedOccupationSegmentContribution_markedJump_horizon
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise} (hne : ξ.NonExplosive)
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hchan : ξ.ConditionalChannelLaw S hflow P initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (hreg : DavisResetOccupationRegular S hflow g)
    (hg : Measurable g) (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentCenteredResetProfile S hflow g p.1 p.2)
    (hPhicont : ∀ z,
      Continuous (davisSegmentCenteredResetProfile S hflow g z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |davisSegmentCenteredResetProfile S hflow g z r -
      davisSegmentCenteredResetProfile S hflow g z r'| ≤ L * |r - r'|)
    (Kf : ℝ≥0 → ℝ) (hKf : ∀ (t : ℝ≥0) (z : DavisState Q n) (r : ℝ),
      r ≤ (t : ℝ) → |davisSegmentCenteredResetProfile S hflow g z r| ≤ Kf t)
    (N : ℕ) :
    Martingale (fun t => davisElapsedOccupationSegmentContribution S hflow ξ hne
      initial g N t) (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) P :=
  martingale_davisElapsedOccupationSegmentContribution_of_conditionalStep hcont
    hgcont (davisSegmentConditionalStepLaw_markedJump_horizon hne hlaw hchan
      hcont hgcont hreg hg Cg hgC hPhimeas hPhicont L hL hlip Kf hKf N)

/-- **The deterministic-cap increment law for the marked jump filtration**
under a profile bound required only below the observation time. -/
theorem davisStoppedElapsedOccupationIncrementLaw_markedJump_horizon
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise} (hne : ξ.NonExplosive)
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hchan : ξ.ConditionalChannelLaw S hflow P initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (hreg : DavisResetOccupationRegular S hflow g)
    (hg : Measurable g) (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentCenteredResetProfile S hflow g p.1 p.2)
    (hPhicont : ∀ z,
      Continuous (davisSegmentCenteredResetProfile S hflow g z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |davisSegmentCenteredResetProfile S hflow g z r -
      davisSegmentCenteredResetProfile S hflow g z r'| ≤ L * |r - r'|)
    (Kf : ℝ≥0 → ℝ) (hKf : ∀ (t : ℝ≥0) (z : DavisState Q n) (r : ℝ),
      r ≤ (t : ℝ) → |davisSegmentCenteredResetProfile S hflow g z r| ≤ Kf t) :
    DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
  DavisStoppedElapsedOccupationIncrementLaw.of_conditional_step_laws hcont
    hgcont (fun N => davisSegmentConditionalStepLaw_markedJump_horizon hne hlaw
      hchan hcont hgcont hreg hg Cg hgC hPhimeas hPhicont L hL hlip Kf hKf N)

/-! ## Instantiation at the linear growth bound

A bounded test function and a bounded intensity give the horizon-dependent
bound `Kf t = 2·Cg·(1 + Λ·t)`, so the three statements above hold with no
hypothesis on the accumulated hazard and no global bound on the profile. -/

/-- The linear growth bound in horizon form. -/
theorem abs_davisSegmentCenteredResetProfile_le_horizon
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {g : DavisState Q n → ℝ}
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (Cg : ℝ) (hgC : ∀ y, |g y| ≤ Cg)
    (Lam : ℝ) (hLam : ∀ z, S.totalIntensity z ≤ Lam)
    (t : ℝ≥0) (z : DavisState Q n) (r : ℝ) (hr : r ≤ (t : ℝ)) :
    |davisSegmentCenteredResetProfile S hflow g z r| ≤
      2 * Cg * (1 + Lam * (t : ℝ)) :=
  abs_davisSegmentCenteredResetProfile_le_of_age_le S hflow hcont hgcont Cg hgC
    Lam hLam ((t : ℝ≥0) : ℝ) t.coe_nonneg z r hr

/-- **The conditional step law of the one-segment martingale for the marked
jump filtration under a bounded test function and a bounded intensity.**  No
bound on the accumulated hazard, and no global bound on the centered reset
profile, is assumed. -/
theorem davisSegmentConditionalStepLaw_markedJump_boundedIntensity
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise} (hne : ξ.NonExplosive)
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hchan : ξ.ConditionalChannelLaw S hflow P initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (hreg : DavisResetOccupationRegular S hflow g)
    (hg : Measurable g) (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg)
    (Lam : ℝ) (hLam : ∀ z, S.totalIntensity z ≤ Lam)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentCenteredResetProfile S hflow g p.1 p.2)
    (hPhicont : ∀ z,
      Continuous (davisSegmentCenteredResetProfile S hflow g z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |davisSegmentCenteredResetProfile S hflow g z r -
      davisSegmentCenteredResetProfile S hflow g z r'| ≤ L * |r - r'|)
    (N : ℕ) :
    DavisSegmentConditionalStepLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g
      N :=
  davisSegmentConditionalStepLaw_markedJump_horizon hne hlaw hchan hcont hgcont
    hreg hg Cg hgC hPhimeas hPhicont L hL hlip
    (fun t => 2 * Cg * (1 + Lam * (t : ℝ)))
    (fun t z r hrle => abs_davisSegmentCenteredResetProfile_le_horizon S hflow
      hcont hgcont Cg hgC Lam hLam t z r hrle) N

/-- **The one-segment martingale for the marked jump filtration under a
bounded test function and a bounded intensity.** -/
theorem martingale_davisElapsedOccupationSegmentContribution_markedJump_boundedIntensity
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise} (hne : ξ.NonExplosive)
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hchan : ξ.ConditionalChannelLaw S hflow P initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (hreg : DavisResetOccupationRegular S hflow g)
    (hg : Measurable g) (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg)
    (Lam : ℝ) (hLam : ∀ z, S.totalIntensity z ≤ Lam)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentCenteredResetProfile S hflow g p.1 p.2)
    (hPhicont : ∀ z,
      Continuous (davisSegmentCenteredResetProfile S hflow g z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |davisSegmentCenteredResetProfile S hflow g z r -
      davisSegmentCenteredResetProfile S hflow g z r'| ≤ L * |r - r'|)
    (N : ℕ) :
    Martingale (fun t => davisElapsedOccupationSegmentContribution S hflow ξ hne
      initial g N t) (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) P :=
  martingale_davisElapsedOccupationSegmentContribution_of_conditionalStep hcont
    hgcont (davisSegmentConditionalStepLaw_markedJump_boundedIntensity hne hlaw
      hchan hcont hgcont hreg hg Cg hgC Lam hLam hPhimeas hPhicont L hL hlip N)

/-- **The deterministic-cap increment law for the marked jump filtration under
a bounded test function and a bounded intensity** — the last structural input
of the elapsed occupation theory, now free of the unsatisfiable hypothesis of a
uniformly bounded accumulated hazard. -/
theorem davisStoppedElapsedOccupationIncrementLaw_markedJump_boundedIntensity
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise} (hne : ξ.NonExplosive)
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hchan : ξ.ConditionalChannelLaw S hflow P initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (hreg : DavisResetOccupationRegular S hflow g)
    (hg : Measurable g) (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg)
    (Lam : ℝ) (hLam : ∀ z, S.totalIntensity z ≤ Lam)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentCenteredResetProfile S hflow g p.1 p.2)
    (hPhicont : ∀ z,
      Continuous (davisSegmentCenteredResetProfile S hflow g z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |davisSegmentCenteredResetProfile S hflow g z r -
      davisSegmentCenteredResetProfile S hflow g z r'| ≤ L * |r - r'|) :
    DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
  DavisStoppedElapsedOccupationIncrementLaw.of_conditional_step_laws hcont
    hgcont (fun N => davisSegmentConditionalStepLaw_markedJump_boundedIntensity
      hne hlaw hchan hcont hgcont hreg hg Cg hgC Lam hLam hPhimeas hPhicont L hL
      hlip N)

end SHS
