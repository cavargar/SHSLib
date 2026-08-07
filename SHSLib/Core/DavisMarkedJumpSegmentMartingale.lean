import SHSLib.Core.DavisMarkedJumpAdapted

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The conditional step law, the one-segment martingale, and the increment
law for the marked jump filtration

Everything the conditional step law asks for is now available for the
observation filtration of the marked jump history: the three integral
identities, the observability of a segment contribution and of the cumulative
jump times.  What is left is integrability, and it comes from a single source:
the bound the centered reset profile puts on the partial occupation
compensator.  A bounded test function has bounded reset increments, so a bound
on the profile bounds the compensator, hence the completed part, the active
part and the conditional active mean; over a finite measure bounded measurable
functions are integrable.

The interface is therefore produced in full, and with it — through the results
already proved from the interface — the martingale property of a single flow
segment and the deterministic-cap increment law, both for a genuine
observation filtration rather than for the full-information one.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Bounds from the profile bound -/

/-- A bound on the centered reset profile bounds the partial occupation
compensator. -/
theorem abs_davisSegmentResetOccupationCompensator_le_of_profile
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg) (K : ℝ)
    (hK : ∀ z r, |davisSegmentCenteredResetProfile S hflow g z r| ≤ K)
    (z : DavisState Q n) (u : ℝ≥0) :
    |davisSegmentResetOccupationCompensator S hflow g z u| ≤ K + 2 * Cg := by
  have h := hK z ((u : ℝ≥0) : ℝ)
  rw [davisSegmentCenteredResetProfile, Real.toNNReal_coe] at h
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

/-! ## Ambient measurability of the two parts -/

/-- The completed part of a segment contribution is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.measurable_segmentCompletedPart
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    {g : DavisState Q n → ℝ} (hg : Measurable g)
    (hreg : DavisResetOccupationRegular S hflow g) (N : ℕ) (t : ℝ≥0) :
    Measurable (davisSegmentCompletedPart S hflow ξ initial g N t) := by
  unfold davisSegmentCompletedPart davisSegmentCompletedContribution
  refine Measurable.ite
    (measurableSet_le (hξ.jumpTime (N + 1)) measurable_const) ?_
    measurable_const
  exact (hξ.realizedResetIncrement S hflow hf hr initial g hg N).sub
    (hreg.measurable_sampled_stoppedCompensator (hf := hf) (hr := hr) hξ initial
      N)

/-- The active part of a segment contribution is measurable. -/
theorem DavisJumpNoise.MeasurableNoise.measurable_segmentActivePart
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {ξ : DavisJumpNoise m Ω}
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    {g : DavisState Q n → ℝ}
    (hreg : DavisResetOccupationRegular S hflow g) (N : ℕ) (t : ℝ≥0) :
    Measurable (davisSegmentActivePart S hflow ξ initial g N t) := by
  unfold davisSegmentActivePart
  refine Measurable.ite
    (measurableSet_le (hξ.jumpTime (N + 1)) measurable_const) measurable_const ?_
  refine Measurable.ite (measurableSet_le (hξ.jumpTime N) measurable_const) ?_
    measurable_const
  exact hreg.stoppedCompensator_measurable.comp
    ((hξ.stateAfterJump S hflow hf hr initial N).prodMk
      (measurable_const.sub (hξ.jumpTime N)))

/-! ## The conditional step law for the marked jump filtration -/

set_option maxHeartbeats 1000000 in
/-- **The conditional step law of the one-segment martingale holds for the
observation filtration of the marked jump history.** -/
theorem davisSegmentConditionalStepLaw_markedJump
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
    (K : ℝ) (hK : ∀ z r,
      |davisSegmentCenteredResetProfile S hflow g z r| ≤ K)
    (N : ℕ) :
    DavisSegmentConditionalStepLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g
      N := by
  classical
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC initial)
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK initial 0)
  have hcompbound := abs_davisSegmentResetOccupationCompensator_le_of_profile S
    hflow g Cg hgC K hK
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
        2 * Cg + (K + 2 * Cg) := by
    intro t ω
    unfold davisSegmentCompletedPart davisSegmentCompletedContribution
    by_cases hend : ξ.jumpTime (N + 1) ω ≤ t
    · rw [if_pos hend]
      calc |davisRealizedResetIncrement S hflow ξ initial g N ω -
              davisSampledResetOccupationCompensator S hflow g ξ initial N ω|
          ≤ |davisRealizedResetIncrement S hflow ξ initial g N ω| +
            |davisSampledResetOccupationCompensator S hflow g ξ initial N ω| :=
            abs_sub _ _
        _ ≤ 2 * Cg + (K + 2 * Cg) :=
            add_le_add (abs_davisRealizedResetIncrement_le S hflow ξ initial g
              Cg hgC N ω) (hcompbound _ _)
    · rw [if_neg hend, abs_zero]
      positivity
  have hactiveb : ∀ (t : ℝ≥0) (ω : Ω),
      |davisSegmentActivePart S hflow ξ initial g N t ω| ≤ K + 2 * Cg := by
    intro t ω
    unfold davisSegmentActivePart
    by_cases hend : ξ.jumpTime (N + 1) ω ≤ t
    · rw [if_pos hend, abs_zero]; positivity
    · rw [if_neg hend]
      by_cases hstart : ξ.jumpTime N ω ≤ t
      · rw [if_pos hstart]; exact hcompbound _ _
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
        (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω)| ≤ K + 2 * Cg := by
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
        ≤ 1 * (K + 2 * Cg) :=
          mul_le_mul hratio (hcompbound z v) (abs_nonneg _) zero_le_one
      _ = K + 2 * Cg := one_mul _
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
      hg Cg hgC hPhimeas hPhicont L hL hlip ((t : ℝ≥0) : ℝ) K
      (fun z r _ => hK z r) N s t hst le_rfl A hA hAsub
  · exact hlaw.markedJump_active_conditional hcont hreg N s t hst (K + 2 * Cg)
      (fun ω => hcompbound _ _) A hA hAsub
  · exact DavisJumpNoise.markedJump_fresh_centered hne hlaw hchan hcont hgcont
      hreg hg Cg hgC hPhimeas hPhicont L hL hlip ((t : ℝ≥0) : ℝ) K
      (fun z r _ => hK z r) N s t le_rfl A hA hAsub

/-! ## Consequences -/

/-- **The one-segment martingale for the marked jump filtration.** -/
theorem martingale_davisElapsedOccupationSegmentContribution_markedJump
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
    (K : ℝ) (hK : ∀ z r,
      |davisSegmentCenteredResetProfile S hflow g z r| ≤ K)
    (N : ℕ) :
    Martingale (fun t => davisElapsedOccupationSegmentContribution S hflow ξ hne
      initial g N t) (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) P :=
  martingale_davisElapsedOccupationSegmentContribution_of_conditionalStep hcont
    hgcont (davisSegmentConditionalStepLaw_markedJump hne hlaw hchan hcont
      hgcont hreg hg Cg hgC hPhimeas hPhicont L hL hlip K hK N)

/-- **The deterministic-cap increment law for the marked jump filtration** —
the last structural input of the elapsed occupation theory, now available for a
genuine observation filtration. -/
theorem davisStoppedElapsedOccupationIncrementLaw_markedJump
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
    (K : ℝ) (hK : ∀ z r,
      |davisSegmentCenteredResetProfile S hflow g z r| ≤ K) :
    DavisStoppedElapsedOccupationIncrementLaw S hflow P
      (ξ.markedJumpFiltration S hflow hf hr hξ hne initial) ξ hne initial g :=
  DavisStoppedElapsedOccupationIncrementLaw.of_conditional_step_laws hcont
    hgcont (fun N => davisSegmentConditionalStepLaw_markedJump hne hlaw hchan
      hcont hgcont hreg hg Cg hgC hPhimeas hPhicont L hL hlip K hK N)

end SHS
