import SHSLib.Core.DavisConditionalHoldingDensityRandomWindow
import SHSLib.Core.DavisSegmentCompletedConditional

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The two segment laws at a history-measurable start age

The conditional laws of the active and of the completed part of a segment
contribution were proved for the start age `u = s − T_N` produced by a
*deterministic* observation time `s`.  Two features of that situation were used:
the segment has already started at `s`, and the age window `(u, u+T]` the
segment must complete in has the deterministic length `T = t − s`.

Neither is available when the segment is observed at the random time at which
it starts — the situation the remaining field of the conditional step law, the
centering of a segment not yet started, leads to.  This module therefore proves
both laws for an arbitrary history-measurable start age `u` and, for the
completed part, an arbitrary bounded history-measurable window length `V`, with
the two features replaced by the minimal hypotheses that make the statements
meaningful:

* the segment has started by the *later* time `t` on the conditioning event;
* the age window closes at the age the segment has reached at `t`, i.e.
  `t − T_N = u + V` on that event.

For the active part nothing but the first is needed, since the weighted
survivor identity already accepts random thresholds.  For the completed part
the density step is the one of the previous module, at a random window length.

The deterministic-observation-time laws are the special case `u = s − T_N`,
`V = t − s`.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## The active part -/

/-- **The conditional law of the active part at a history-measurable start
age.**  On a pre-jump history event at index `N` on which segment `N` has
started by `t`, the mean of the active part at `t`, restricted to the event
that the segment survives the start age `u`, is the mean of the conditional
active mean from `u` to the age reached at `t`. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.setIntegral_segmentActivePart_startAge
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hreg : DavisResetOccupationRegular S hflow g)
    (N : ℕ) (t : ℝ≥0) (uu : Ω → ℝ≥0)
    (huumeas : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N]
      uu)
    (huv : ∀ ω, uu ω ≤ t - ξ.jumpTime N ω)
    (B : Set Ω)
    (hB : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N] B)
    (hBt : ∀ ω ∈ B, ξ.jumpTime N ω ≤ t)
    (K : ℝ)
    (hK : ∀ ω, |davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial N ω)
      (t - ξ.jumpTime N ω)| ≤ K) :
    ∫ ω in B ∩ {ω | uu ω < ξ.holdingTime N ω},
        davisSegmentActivePart S hflow ξ initial g N t ω ∂P =
      ∫ ω in B ∩ {ω | uu ω < ξ.holdingTime N ω},
        davisSegmentConditionalActiveMean S hflow g
          (davisStateAfterJump S hflow ξ initial N ω)
          (uu ω) (t - ξ.jumpTime N ω) ∂P := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  set zN : Ω → DavisState Q n :=
    fun ω => davisStateAfterJump S hflow ξ initial N ω with hzN
  set vv : Ω → ℝ≥0 := fun ω => t - ξ.jumpTime N ω with hvv
  set cmp : Ω → ℝ :=
    fun ω => davisSegmentResetOccupationCompensator S hflow g (zN ω) (vv ω)
    with hcmp
  set surU : Ω → ℝ := fun ω => davisSegmentSurvivor S hflow (zN ω) (uu ω)
    with hsurU
  set surV : Ω → ℝ := fun ω => davisSegmentSurvivor S hflow (zN ω) (vv ω)
    with hsurV
  have hm : (F N : MeasurableSpace Ω) ≤ mΩ := F.le N
  -- measurability in the pre-jump history
  have hTmeas : Measurable[F N] (ξ.jumpTime N) :=
    ξ.measurable_jumpTime_preJumpHistory S hflow hf hr hξ initial N
  have hzmeas : Measurable[F N] zN :=
    (DavisPreJumpHistory.measurable_currentState N).comp
      (ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial N)
  have hvmeas : Measurable[F N] vv := measurable_const.sub hTmeas
  have hcmpmeas : Measurable[F N] cmp :=
    hreg.stoppedCompensator_measurable.comp (hzmeas.prodMk hvmeas)
  have hsurvmeas : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2 := hreg.survivor_measurable
  have hsurUmeas : Measurable[F N] surU :=
    hsurvmeas.comp (hzmeas.prodMk huumeas)
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
    measurableSet_lt (huumeas.mono hm le_rfl) (hξ.holdingTime N)
  have hVm : MeasurableSet {ω | vv ω < ξ.holdingTime N ω} :=
    measurableSet_lt (hvmeas.mono hm le_rfl) (hξ.holdingTime N)
  have hBm : MeasurableSet B := hm _ hB
  -- the left-hand side
  have hLpt : ∀ ω ∈ B ∩ {ω | uu ω < ξ.holdingTime N ω},
      davisSegmentActivePart S hflow ξ initial g N t ω =
        {ω | vv ω < ξ.holdingTime N ω}.indicator cmp ω := by
    rintro ω ⟨hωB, -⟩
    have hstart : ξ.jumpTime N ω ≤ t := hBt ω hωB
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
      _ ≤ 1 * |cmp ω| := mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
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
      huumeas B hB wgt hwgtmeas K hwgtK
    rw [h]
    refine setIntegral_congr_fun hBm fun ω _ => ?_
    have hUdef : davisSegmentSurvivor S hflow (zN ω) (uu ω) = surU ω := rfl
    have hUne : surU ω ≠ 0 := ne_of_gt (hsurUpos ω)
    rw [hnext ω (uu ω), hwgt, hUdef]
    field_simp
  rw [hL1, hL2, hR1, hR2]

/-! ## The completed part -/

set_option maxHeartbeats 4000000 in
/-- **The conditional law of the completed part at a history-measurable start
age and window length.**  On a pre-jump history event at index `N` on which
segment `N` has started by `t` and on which the age reached at `t` is `u + V`,
the mean of the completed part at `t`, restricted to the event that the segment
survives the start age `u`, is the mean of the conditional completed mean over
the window. -/
theorem DavisJumpNoise.setIntegral_segmentCompletedPart_startAge
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    [S.IntensitiesMeasurable]
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hchan : ξ.ConditionalChannelLaw S hflow P initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2)
    (hg : Measurable g) (Cg : ℝ) (hgC : ∀ z, |g z| ≤ Cg)
    (hPhimeas : Measurable fun p : DavisState Q n × ℝ =>
      davisSegmentCenteredResetProfile S hflow g p.1 p.2)
    (hPhicont : ∀ z,
      Continuous (davisSegmentCenteredResetProfile S hflow g z))
    (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ z r r', |davisSegmentCenteredResetProfile S hflow g z r -
      davisSegmentCenteredResetProfile S hflow g z r'| ≤ L * |r - r'|)
    (Rmax K : ℝ) (hK : ∀ z r, r ≤ Rmax →
      |davisSegmentCenteredResetProfile S hflow g z r| ≤ K)
    (N : ℕ) (t : ℝ≥0) (hRmax : ((t : ℝ≥0) : ℝ) ≤ Rmax) (uu V : Ω → ℝ≥0)
    (huumeas : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N]
      uu)
    (hVmeasF : Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N]
      V)
    (Tmax : ℝ≥0) (hVle : ∀ ω, V ω ≤ Tmax)
    (B : Set Ω)
    (hB : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N] B)
    (hBt : ∀ ω ∈ B, ξ.jumpTime N ω ≤ t)
    (hwin : ∀ ω ∈ B, t - ξ.jumpTime N ω = uu ω + V ω) :
    ∫ ω in B ∩ {ω | uu ω < ξ.holdingTime N ω},
        davisSegmentCompletedPart S hflow ξ initial g N t ω ∂P =
      ∫ ω in B ∩ {ω | uu ω < ξ.holdingTime N ω},
        davisSegmentConditionalCompletedMean S hflow g
          (davisStateAfterJump S hflow ξ initial N ω)
          (uu ω) (t - ξ.jumpTime N ω) ∂P := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  have hm : (F N : MeasurableSpace Ω) ≤ mΩ := F.le N
  have hBm : MeasurableSet B := hm _ hB
  set Phi : DavisState Q n → ℝ → ℝ :=
    davisSegmentCenteredResetProfile S hflow g with hPhi
  set zz : Ω → DavisState Q n :=
    fun ω => davisStateAfterJump S hflow ξ initial N ω with hzz
  set vv : Ω → ℝ≥0 := fun ω => t - ξ.jumpTime N ω with hvv
  set hh : Ω → ℝ≥0 := ξ.holdingTime N with hhh
  have hhm : Measurable hh := hξ.holdingTime N
  have hTmeas : Measurable[F N] (ξ.jumpTime N) :=
    ξ.measurable_jumpTime_preJumpHistory S hflow hf hr hξ initial N
  have hzF : Measurable[F N] zz :=
    (DavisPreJumpHistory.measurable_currentState N).comp
      (ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial N)
  have hzm : Measurable zz := hzF.mono hm le_rfl
  have hum : Measurable uu := huumeas.mono hm le_rfl
  have hVm : Measurable V := hVmeasF.mono hm le_rfl
  have hK0 : 0 ≤ K :=
    le_trans (abs_nonneg _) (hK initial 0 (le_trans t.coe_nonneg hRmax))
  -- on the conditioning event the age window closes below the horizon
  have hageB : ∀ ω ∈ B, ((uu ω + V ω : ℝ≥0) : ℝ) ≤ Rmax := by
    intro ω hω
    have hle : uu ω + V ω ≤ t := by
      rw [← hwin ω hω]
      exact tsub_le_self
    exact le_trans (by exact_mod_cast hle) hRmax
  -- measurable sets
  have hSum : MeasurableSet {ω | uu ω < hh ω} := measurableSet_lt hum hhm
  have hWm : MeasurableSet {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω} := by
    have hEq : {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω} =
        {ω | uu ω < hh ω} \ {ω | uu ω + V ω < hh ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]
    exact hEq ▸ hSum.diff (measurableSet_lt (hum.add hVm) hhm)
  -- Step 1: the completed part is the realized centered reset on the window
  have hstep1 : ∫ ω in B ∩ {ω | uu ω < hh ω},
        davisSegmentCompletedPart S hflow ξ initial g N t ω ∂P =
      ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
        (davisRealizedResetIncrement S hflow ξ initial g N ω -
          davisSampledResetOccupationCompensator S hflow g ξ initial N ω) ∂P := by
    have hpt : ∀ ω ∈ B ∩ {ω | uu ω < hh ω},
        davisSegmentCompletedPart S hflow ξ initial g N t ω =
          {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω}.indicator
            (fun ω => davisRealizedResetIncrement S hflow ξ initial g N ω -
              davisSampledResetOccupationCompensator S hflow g ξ initial N ω)
            ω := by
      rintro ω ⟨hωB, hωS⟩
      have hstart : ξ.jumpTime N ω ≤ t := hBt ω hωB
      have hiff : ξ.jumpTime (N + 1) ω ≤ t ↔ hh ω ≤ vv ω := by
        constructor
        · intro hc
          by_contra hcon
          exact ((davisSegmentActive_iff_age_lt_holdingTime ξ N t ω hstart).2
            (not_le.1 hcon)) hc
        · intro hc
          by_contra hcon
          exact absurd hc (not_le.2
            ((davisSegmentActive_iff_age_lt_holdingTime ξ N t ω hstart).1 hcon))
      unfold davisSegmentCompletedPart davisSegmentCompletedContribution
      by_cases hend : ξ.jumpTime (N + 1) ω ≤ t
      · have hmem : ω ∈ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω} := by
          refine ⟨hωS, ?_⟩
          rw [← hwin ω hωB]
          exact hiff.1 hend
        rw [if_pos hend, Set.indicator_of_mem hmem]
      · have hnot : ω ∉ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω} := by
          intro hmem
          refine hend (hiff.2 ?_)
          have hvvB : vv ω = uu ω + V ω := hwin ω hωB
          rw [hvvB]
          exact hmem.2
        rw [if_neg hend, Set.indicator_of_notMem hnot]
    have hsets : (B ∩ {ω | uu ω < hh ω}) ∩
        {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω} =
        B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω} := by
      ext ω
      constructor
      · rintro ⟨⟨hωB, -⟩, hωW⟩
        exact ⟨hωB, hωW⟩
      · rintro ⟨hωB, hωW⟩
        exact ⟨⟨hωB, hωW.1⟩, hωW⟩
    rw [setIntegral_congr_fun (hBm.inter hSum) hpt,
      MeasureTheory.setIntegral_indicator hWm, hsets]
  -- Step 2: the channel step replaces the realized reset by its mean
  have hpreChan : MeasurableSet[ξ.preChannelSpace S hflow initial N]
      (B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω}) := by
    have hBpre : MeasurableSet[ξ.preChannelSpace S hflow initial N] B :=
      (ξ.preJumpHistorySpace_le_preChannel S hflow initial N) B hB
    have hupre : Measurable[ξ.preChannelSpace S hflow initial N] uu :=
      huumeas.mono (ξ.preJumpHistorySpace_le_preChannel S hflow initial N) le_rfl
    have hVpre : Measurable[ξ.preChannelSpace S hflow initial N] V :=
      hVmeasF.mono (ξ.preJumpHistorySpace_le_preChannel S hflow initial N) le_rfl
    have hhpre : Measurable[ξ.preChannelSpace S hflow initial N] hh :=
      DavisJumpNoise.holdingTime_measurable_preChannel S hflow ξ initial N
    have hEq : {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω} =
        {ω | uu ω < hh ω} \ {ω | uu ω + V ω < hh ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]
    refine hBpre.inter ?_
    rw [hEq]
    exact (measurableSet_lt hupre hhpre).diff
      (measurableSet_lt (hupre.add hVpre) hhpre)
  have hstep2 : ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
        davisRealizedResetIncrement S hflow ξ initial g N ω ∂P =
      ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
        davisExpectedResetIncrement S g
          (davisStateBeforeJump S hflow ξ initial N ω) ∂P := by
    have h := hchan.setIntegral_realizedResetIncrement_weighted hf hr hξ g hg
      Cg hgC N (B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω}) hpreChan
      (fun _ => (1 : ℝ)) measurable_const 1 (fun _ => by norm_num)
    simpa using h
  -- the integrand on the window is the centered reset profile at the age
  have hprofile : ∀ ω,
      davisExpectedResetIncrement S g
          (davisStateBeforeJump S hflow ξ initial N ω) -
        davisSampledResetOccupationCompensator S hflow g ξ initial N ω =
      Phi (zz ω) ((hh ω : ℝ≥0) : ℝ) := by
    intro ω
    rw [hPhi, davisSegmentCenteredResetProfile]
    simp only [Real.toNNReal_coe]
    rfl
  -- Step 3: the density form of the conditional holding-time law
  have hstep3 : ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
        Phi (zz ω) ((hh ω : ℝ≥0) : ℝ) ∂P =
      ∫ ω in B, davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) (V ω) ∂P :=
    hlaw.setIntegral_holdingTime_density_randomWindow_of_age_le hcont hsurv Phi
      hPhimeas hPhicont L hL hlip Rmax K hK N uu V huumeas hVmeasF Tmax hVle
      B hB hageB
  -- boundedness of the normalized expected reset increment
  have hEbound : ∀ z : DavisState Q n,
      |davisExpectedResetIncrement S g z| ≤ 2 * Cg := by
    intro z
    have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC z)
    unfold davisExpectedResetIncrement
    calc |∑ l : Fin m, davisChannelProbability S z l *
            (g (S.resetDavisState l z) - g z)|
        ≤ ∑ l : Fin m, |davisChannelProbability S z l *
            (g (S.resetDavisState l z) - g z)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin m, davisChannelProbability S z l * (2 * Cg) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [abs_mul, abs_of_nonneg (davisChannelProbability_nonneg S z l)]
          refine mul_le_mul_of_nonneg_left ?_
            (davisChannelProbability_nonneg S z l)
          calc |g (S.resetDavisState l z) - g z|
              ≤ |g (S.resetDavisState l z)| + |g z| := abs_sub _ _
            _ ≤ Cg + Cg := add_le_add (hgC _) (hgC _)
            _ = 2 * Cg := by ring
      _ = (∑ l : Fin m, davisChannelProbability S z l) * (2 * Cg) := by
          rw [Finset.sum_mul]
      _ ≤ 1 * (2 * Cg) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          by_cases hz : S.totalIntensity z = 0
          · have hzero : ∀ l : Fin m, davisChannelProbability S z l = 0 := by
              intro l
              unfold davisChannelProbability
              rw [hz, div_zero]
            simp [hzero]
          · rw [sum_davisChannelProbability S z hz]
      _ = 2 * Cg := one_mul _
  -- integrability facts
  have hboundint : ∀ (f : Ω → ℝ), Measurable f → ∀ (c : ℝ), (∀ ω, |f ω| ≤ c) →
      ∀ D : Set Ω, IntegrableOn f D P := by
    intro f hfm c hfc D
    refine Integrable.integrableOn ?_
    refine (integrable_const (max c 0)).mono' hfm.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact le_trans (hfc ω) (le_max_left c 0)
  -- the same, with the bound required only on the integration set
  have hboundintOn : ∀ (f : Ω → ℝ), Measurable f → ∀ (c : ℝ) (D : Set Ω),
      MeasurableSet D → (∀ ω ∈ D, |f ω| ≤ c) → IntegrableOn f D P := by
    intro f hfm c D hD hfc
    refine (integrable_const (max c 0)).mono' hfm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hD] with ω hω
    rw [Real.norm_eq_abs]
    exact le_trans (hfc ω hω) (le_max_left c 0)
  have hzbm : Measurable (davisStateBeforeJump S hflow ξ initial N) :=
    hξ.stateBeforeJump S hflow hf hr initial N
  have hEm : Measurable fun ω => davisExpectedResetIncrement S g
      (davisStateBeforeJump S hflow ξ initial N ω) :=
    (measurable_davisExpectedResetIncrement S hr g hg).comp hzbm
  have hDm : Measurable (davisRealizedResetIncrement S hflow ξ initial g N) :=
    hξ.realizedResetIncrement S hflow hf hr initial g hg N
  have hPhiωm : Measurable fun ω => Phi (zz ω) ((hh ω : ℝ≥0) : ℝ) :=
    hPhimeas.comp (hzm.prodMk (measurable_coe_nnreal_real.comp hhm))
  have hCm : Measurable fun ω =>
      davisSampledResetOccupationCompensator S hflow g ξ initial N ω := by
    have heq : (fun ω => davisSampledResetOccupationCompensator S hflow g ξ
        initial N ω) = fun ω => davisExpectedResetIncrement S g
          (davisStateBeforeJump S hflow ξ initial N ω) -
            Phi (zz ω) ((hh ω : ℝ≥0) : ℝ) := by
      funext ω
      rw [← hprofile ω]
      ring
    rw [heq]
    exact hEm.sub hPhiωm
  have hDbound : ∀ ω, |davisRealizedResetIncrement S hflow ξ initial g N ω| ≤
      2 * Cg := by
    intro ω
    unfold davisRealizedResetIncrement
    calc |g (S.resetDavisState (ξ.channel N ω)
          (davisStateBeforeJump S hflow ξ initial N ω)) -
        g (davisStateBeforeJump S hflow ξ initial N ω)|
        ≤ |g (S.resetDavisState (ξ.channel N ω)
            (davisStateBeforeJump S hflow ξ initial N ω))| +
          |g (davisStateBeforeJump S hflow ξ initial N ω)| := abs_sub _ _
      _ ≤ Cg + Cg := add_le_add (hgC _) (hgC _)
      _ = 2 * Cg := by ring
  have hCbound : ∀ ω ∈ B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
      |davisSampledResetOccupationCompensator S hflow g ξ
      initial N ω| ≤ 2 * Cg + K := by
    intro ω hωD
    have hhle : ((hh ω : ℝ≥0) : ℝ) ≤ Rmax := by
      refine le_trans ?_ (hageB ω hωD.1)
      exact_mod_cast hωD.2.2
    have h := hprofile ω
    have h1 : davisSampledResetOccupationCompensator S hflow g ξ initial N ω =
        davisExpectedResetIncrement S g
          (davisStateBeforeJump S hflow ξ initial N ω) -
            Phi (zz ω) ((hh ω : ℝ≥0) : ℝ) := by
      rw [← h]; ring
    rw [h1]
    calc |davisExpectedResetIncrement S g
          (davisStateBeforeJump S hflow ξ initial N ω) -
            Phi (zz ω) ((hh ω : ℝ≥0) : ℝ)|
        ≤ |davisExpectedResetIncrement S g
            (davisStateBeforeJump S hflow ξ initial N ω)| +
          |Phi (zz ω) ((hh ω : ℝ≥0) : ℝ)| := abs_sub _ _
      _ ≤ 2 * Cg + K := add_le_add (hEbound _) (hK _ _ hhle)
  -- Step 4: the conditional completed mean on the survival event
  set PhiT : DavisState Q n → ℝ → ℝ := davisTruncatedProfile Phi Rmax with hPhiT
  have hPhiTmeas : Measurable fun p : DavisState Q n × ℝ => PhiT p.1 p.2 :=
    measurable_davisTruncatedProfile hPhimeas Rmax
  have hPhiTcont : ∀ z, Continuous (PhiT z) :=
    continuous_davisTruncatedProfile hPhicont Rmax
  have hPhiTK : ∀ z r, |PhiT z r| ≤ K := abs_davisTruncatedProfile_le hK
  have hwinmeasF : Measurable[F N] fun ω =>
      davisHazardWindowIntegral S hflow PhiT (zz ω) (uu ω) (V ω) :=
    (measurable_davisHazardWindowIntegral_triple S hflow hf hsurv PhiT
      hPhiTmeas).comp ((hzF.prodMk huumeas).prodMk hVmeasF)
  have hsurUF : Measurable[F N] fun ω =>
      davisSegmentSurvivor S hflow (zz ω) (uu ω) :=
    hsurv.comp (hzF.prodMk huumeas)
  set wgt : Ω → ℝ := fun ω =>
    (davisSegmentSurvivor S hflow (zz ω) (uu ω))⁻¹ *
      davisHazardWindowIntegral S hflow PhiT (zz ω) (uu ω) (V ω) with hwgt
  have hwgtF : Measurable[F N] wgt := (hsurUF.inv).mul hwinmeasF
  have hwgtK : ∀ ω, |wgt ω| ≤ K := by
    intro ω
    have hpos : 0 < davisSegmentSurvivor S hflow (zz ω) (uu ω) :=
      davisSegmentSurvivor_pos S hflow (zz ω) (uu ω)
    have hb := abs_davisHazardWindowIntegral_le_mul_survivor_sub S hflow hcont
      PhiT hPhiTcont K hPhiTK (zz ω) (uu ω) (V ω)
    have hposv : 0 < davisSegmentSurvivor S hflow (zz ω) (uu ω + V ω) :=
      davisSegmentSurvivor_pos S hflow (zz ω) (uu ω + V ω)
    rw [hwgt, abs_mul, abs_of_pos (inv_pos.2 hpos)]
    have hK1 : |davisHazardWindowIntegral S hflow PhiT (zz ω) (uu ω) (V ω)| ≤
        K * davisSegmentSurvivor S hflow (zz ω) (uu ω) := by
      refine le_trans hb ?_
      have hle : davisSegmentSurvivor S hflow (zz ω) (uu ω) -
          davisSegmentSurvivor S hflow (zz ω) (uu ω + V ω) ≤
          davisSegmentSurvivor S hflow (zz ω) (uu ω) := by linarith
      exact mul_le_mul_of_nonneg_left hle hK0
    calc (davisSegmentSurvivor S hflow (zz ω) (uu ω))⁻¹ *
          |davisHazardWindowIntegral S hflow PhiT (zz ω) (uu ω) (V ω)|
        ≤ (davisSegmentSurvivor S hflow (zz ω) (uu ω))⁻¹ *
            (K * davisSegmentSurvivor S hflow (zz ω) (uu ω)) :=
          mul_le_mul_of_nonneg_left hK1 (le_of_lt (inv_pos.2 hpos))
      _ = K := by field_simp
  have hstep4 : ∫ ω in B ∩ {ω | uu ω < hh ω}, wgt ω ∂P =
      ∫ ω in B, davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) (V ω) ∂P := by
    have h := hlaw.setIntegral_lt_holdingTime_weighted hcont hsurv N uu huumeas
      B hB wgt hwgtF K hwgtK
    rw [h]
    refine setIntegral_congr_fun hBm fun ω hω => ?_
    have hpos : davisSegmentSurvivor S hflow (zz ω) (uu ω) ≠ 0 :=
      ne_of_gt (davisSegmentSurvivor_pos S hflow (zz ω) (uu ω))
    show wgt ω * davisSegmentSurvivor S hflow (zz ω) (uu ω) = _
    rw [hwgt]
    simp only [hPhiT]
    rw [davisHazardWindowIntegral_davisTruncatedProfile S hflow Phi (zz ω)
      (uu ω) (V ω) (hageB ω hω)]
    field_simp
  -- assemble the left-hand side
  have hLHS : ∫ ω in B ∩ {ω | uu ω < hh ω},
      davisSegmentCompletedPart S hflow ξ initial g N t ω ∂P =
      ∫ ω in B, davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) (V ω) ∂P := by
    rw [hstep1]
    have hsplit : ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
        (davisRealizedResetIncrement S hflow ξ initial g N ω -
          davisSampledResetOccupationCompensator S hflow g ξ initial N ω) ∂P =
        (∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
            davisRealizedResetIncrement S hflow ξ initial g N ω ∂P) -
          ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
            davisSampledResetOccupationCompensator S hflow g ξ initial N ω
              ∂P :=
      integral_sub (hboundint _ hDm (2 * Cg) hDbound _)
        (hboundintOn _ hCm (2 * Cg + K) _ (hBm.inter hWm) hCbound)
    have hjoin : (∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
          davisExpectedResetIncrement S g
            (davisStateBeforeJump S hflow ξ initial N ω) ∂P) -
        (∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
          davisSampledResetOccupationCompensator S hflow g ξ initial N ω ∂P) =
        ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + V ω},
          Phi (zz ω) ((hh ω : ℝ≥0) : ℝ) ∂P := by
      rw [← integral_sub (hboundint _ hEm (2 * Cg) (fun ω => hEbound _) _)
        (hboundintOn _ hCm (2 * Cg + K) _ (hBm.inter hWm) hCbound)]
      exact setIntegral_congr_fun (hBm.inter hWm) fun ω _ => hprofile ω
    rw [hsplit, hstep2, hjoin, hstep3]
  -- assemble the right-hand side
  have hRHS : ∫ ω in B ∩ {ω | uu ω < hh ω},
      davisSegmentConditionalCompletedMean S hflow g (zz ω) (uu ω) (vv ω) ∂P =
      ∫ ω in B, davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) (V ω) ∂P := by
    rw [← hstep4]
    refine setIntegral_congr_fun (hBm.inter hSum) fun ω hω => ?_
    have hvvω : vv ω = uu ω + V ω := hwin ω hω.1
    have hWI : davisHazardWindowIntegral S hflow PhiT (zz ω) (uu ω) (V ω) =
        davisHazardWindowIntegral S hflow
          (davisSegmentCenteredResetProfile S hflow g) (zz ω) (uu ω) (V ω) :=
      davisHazardWindowIntegral_davisTruncatedProfile S hflow
        (davisSegmentCenteredResetProfile S hflow g) (zz ω) (uu ω) (V ω)
        (hageB ω hω.1)
    rw [hvvω,
      davisSegmentConditionalCompletedMean_eq_windowIntegral S hflow g
        (zz ω) (uu ω) (V ω)]
    show _ = (davisSegmentSurvivor S hflow (zz ω) (uu ω))⁻¹ *
      davisHazardWindowIntegral S hflow PhiT (zz ω) (uu ω) (V ω)
    rw [hWI]
  rw [hLHS, hRHS]

end SHS
