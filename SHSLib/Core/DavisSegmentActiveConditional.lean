import SHSLib.Core.DavisConditionalHoldingWeighted
import SHSLib.Core.DavisOneSegmentConditionalStep

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The conditional law of the active part

The conditional step law of the one-segment martingale asks, among other
things, that on an event of the observation filtration on which segment `N` is
still running at time `s`, the *active part* of the contribution at a later
time `t` integrate to the conditional active mean

`Sur(u)⁻¹ · Sur(v) · comp(v)`,      `u = s − T_N`,  `v = t − T_N`.

This module discharges that field for the events that the marked jump history
produces: an event of the pre-jump history at index `N`, on which the segment
has started, intersected with the survival event `{u < h_N}`.

The proof is the weighted survivor identity of the previous module applied
twice.  On the left, the active part is the partial occupation compensator
carried on the survival event at the *later* age `v`, so the identity with
threshold `v` turns it into the survivor-weighted compensator `Sur(v)·comp(v)`
integrated over the history event.  On the right, the conditional active mean
is a history-measurable weight, so the identity with threshold `u` turns the
integral into `Sur(u) · Sur(u)⁻¹ · Sur(v) · comp(v)`, which is the same thing.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- **The conditional law of the active part on a history survival event.**
On the part of a pre-jump history event at index `N` on which segment `N` is
still running at `s`, the mean of the active part at a later time `t` is the
mean of the conditional active mean. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_segmentActivePart
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hreg : DavisResetOccupationRegular S hflow g)
    (N : ℕ) (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set Ω)
    (hB : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N] B)
    (hBstart : ∀ ω ∈ B, ξ.jumpTime N ω ≤ s)
    (K : ℝ)
    (hK : ∀ ω, |davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial N ω)
      (t - ξ.jumpTime N ω)| ≤ K) :
    ∫ ω in B ∩ {ω | s - ξ.jumpTime N ω < ξ.holdingTime N ω},
        davisSegmentActivePart S hflow ξ initial g N t ω ∂P =
      ∫ ω in B ∩ {ω | s - ξ.jumpTime N ω < ξ.holdingTime N ω},
        davisSegmentConditionalActiveMean S hflow g
          (davisStateAfterJump S hflow ξ initial N ω)
          (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω) ∂P := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  set zN : Ω → DavisState Q n :=
    fun ω => davisStateAfterJump S hflow ξ initial N ω with hzN
  set uu : Ω → ℝ≥0 := fun ω => s - ξ.jumpTime N ω with huu
  set vv : Ω → ℝ≥0 := fun ω => t - ξ.jumpTime N ω with hvv
  set cmp : Ω → ℝ :=
    fun ω => davisSegmentResetOccupationCompensator S hflow g (zN ω) (vv ω)
    with hcmp
  set surU : Ω → ℝ := fun ω => davisSegmentSurvivor S hflow (zN ω) (uu ω)
    with hsurU
  set surV : Ω → ℝ := fun ω => davisSegmentSurvivor S hflow (zN ω) (vv ω)
    with hsurV
  have hm : (F N : MeasurableSpace Ω) ≤ mΩ := F.le N
  have huv : ∀ ω, uu ω ≤ vv ω := fun ω => tsub_le_tsub_right hst _
  -- measurability in the pre-jump history
  have hTmeas : Measurable[F N] (ξ.jumpTime N) :=
    ξ.measurable_jumpTime_preJumpHistory S hflow hf hr hξ initial N
  have hzmeas : Measurable[F N] zN :=
    (DavisPreJumpHistory.measurable_currentState N).comp
      (ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial N)
  have humeas : Measurable[F N] uu := measurable_const.sub hTmeas
  have hvmeas : Measurable[F N] vv := measurable_const.sub hTmeas
  have hcmpmeas : Measurable[F N] cmp :=
    hreg.stoppedCompensator_measurable.comp (hzmeas.prodMk hvmeas)
  have hsurvmeas : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2 := hreg.survivor_measurable
  have hsurUmeas : Measurable[F N] surU :=
    hsurvmeas.comp (hzmeas.prodMk humeas)
  have hsurVmeas : Measurable[F N] surV :=
    hsurvmeas.comp (hzmeas.prodMk hvmeas)
  -- elementary facts about the survivor factors
  have hsurUpos : ∀ ω, 0 < surU ω := fun ω => davisSegmentSurvivor_pos _ _ _ _
  have hsurVpos : ∀ ω, 0 < surV ω := fun ω => davisSegmentSurvivor_pos _ _ _ _
  have hsurVU : ∀ ω, surV ω ≤ surU ω := fun ω =>
    davisSegmentSurvivor_antitone S hflow hcont (zN ω) (huv ω)
  have hnext : ∀ (ω : Ω) (x : ℝ≥0),
      (davisPreJumpHistory S hflow ξ initial N ω).nextSurvivor S hflow x =
        davisSegmentSurvivor S hflow (zN ω) x := fun _ _ => rfl
  have hVsub : {ω | vv ω < ξ.holdingTime N ω} ⊆
      {ω | uu ω < ξ.holdingTime N ω} := fun ω hω =>
    lt_of_le_of_lt (huv ω) hω
  have hUm : MeasurableSet {ω | uu ω < ξ.holdingTime N ω} :=
    measurableSet_lt (humeas.mono hm le_rfl) (hξ.holdingTime N)
  have hVm : MeasurableSet {ω | vv ω < ξ.holdingTime N ω} :=
    measurableSet_lt (hvmeas.mono hm le_rfl) (hξ.holdingTime N)
  have hBm : MeasurableSet B := hm _ hB
  -- the left-hand side
  have hLpt : ∀ ω ∈ B ∩ {ω | uu ω < ξ.holdingTime N ω},
      davisSegmentActivePart S hflow ξ initial g N t ω =
        {ω | vv ω < ξ.holdingTime N ω}.indicator cmp ω := by
    rintro ω ⟨hωB, -⟩
    have hstart : ξ.jumpTime N ω ≤ t := le_trans (hBstart ω hωB) hst
    unfold davisSegmentActivePart
    by_cases hend : ξ.jumpTime (N + 1) ω ≤ t
    · have hnot : ω ∉ {ω | vv ω < ξ.holdingTime N ω} := by
        simp only [Set.mem_setOf_eq]
        rw [← davisSegmentActive_iff_age_lt_holdingTime ξ N t ω hstart]
        exact not_not_intro hend
      rw [if_pos hend, Set.indicator_of_notMem hnot]
    · have hmem : ω ∈ {ω | vv ω < ξ.holdingTime N ω} :=
        (davisSegmentActive_iff_age_lt_holdingTime ξ N t ω hstart).1 hend
      rw [if_neg hend, if_pos hstart, Set.indicator_of_mem hmem]
  have hL1 : ∫ ω in B ∩ {ω | uu ω < ξ.holdingTime N ω},
      davisSegmentActivePart S hflow ξ initial g N t ω ∂P =
        ∫ ω in B ∩ {ω | vv ω < ξ.holdingTime N ω}, cmp ω ∂P := by
    rw [setIntegral_congr_fun (hBm.inter hUm) hLpt,
      MeasureTheory.setIntegral_indicator hVm]
    have hset : (B ∩ {ω | uu ω < ξ.holdingTime N ω}) ∩
        {ω | vv ω < ξ.holdingTime N ω} = B ∩ {ω | vv ω < ξ.holdingTime N ω} := by
      ext ω
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hVsub h.2⟩, h.2⟩⟩
    rw [hset]
  have hL2 : ∫ ω in B ∩ {ω | vv ω < ξ.holdingTime N ω}, cmp ω ∂P =
      ∫ ω in B, cmp ω * surV ω ∂P := by
    have h := hlaw.setIntegral_lt_holdingTime_weighted hcont hsurvmeas N vv
      hvmeas B hB cmp hcmpmeas K hK
    rw [h]
    exact setIntegral_congr_fun hBm fun ω _ => by rw [hnext ω (vv ω)]
  -- the right-hand side
  set wgt : Ω → ℝ := fun ω => (surU ω)⁻¹ * surV ω * cmp ω with hwgt
  have hwgtmeas : Measurable[F N] wgt :=
    ((hsurUmeas.inv).mul hsurVmeas).mul hcmpmeas
  have hwgtK : ∀ ω, |wgt ω| ≤ K := by
    intro ω
    have hratio : (surU ω)⁻¹ * surV ω ≤ 1 := by
      rw [inv_mul_le_iff₀ (hsurUpos ω)]
      simpa using hsurVU ω
    have hratio0 : 0 ≤ (surU ω)⁻¹ * surV ω :=
      le_of_lt (mul_pos (inv_pos.2 (hsurUpos ω)) (hsurVpos ω))
    calc |wgt ω| = ((surU ω)⁻¹ * surV ω) * |cmp ω| := by
          rw [hwgt, abs_mul, abs_of_nonneg hratio0]
      _ ≤ 1 * |cmp ω| := by
          exact mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
      _ = |cmp ω| := one_mul _
      _ ≤ K := hK ω
  have hR1 : ∫ ω in B ∩ {ω | uu ω < ξ.holdingTime N ω},
      davisSegmentConditionalActiveMean S hflow g (zN ω) (uu ω) (vv ω) ∂P =
        ∫ ω in B ∩ {ω | uu ω < ξ.holdingTime N ω}, wgt ω ∂P := by
    refine setIntegral_congr_fun (hBm.inter hUm) fun ω _ => ?_
    rfl
  have hR2 : ∫ ω in B ∩ {ω | uu ω < ξ.holdingTime N ω}, wgt ω ∂P =
      ∫ ω in B, cmp ω * surV ω ∂P := by
    have h := hlaw.setIntegral_lt_holdingTime_weighted hcont hsurvmeas N uu
      humeas B hB wgt hwgtmeas K hwgtK
    rw [h]
    refine setIntegral_congr_fun hBm fun ω _ => ?_
    have hUdef : davisSegmentSurvivor S hflow (zN ω) (uu ω) = surU ω := rfl
    have hUne : surU ω ≠ 0 := ne_of_gt (hsurUpos ω)
    rw [hnext ω (uu ω), hwgt, hUdef]
    field_simp
  rw [hL1, hL2, hR1, hR2]

end SHS
