import SHSLib.Core.DavisConditionalHoldingDensity
import SHSLib.Core.DavisProfileTruncationCore
import SHSLib.Core.DavisConditionalChannelWeighted
import SHSLib.Core.DavisSegmentActiveConditional

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The conditional law of the completed part

The conditional step law of the one-segment martingale has two integral
identities.  The one for the *active* part was discharged from the weighted
survivor identity.  This module discharges the one for the **completed** part:
on the part of a pre-jump history event at index `N` on which segment `N` is
still running at the observation time `s`, the realized centered reset carried
at a later time `t` integrates to the conditional completed mean

`Sur(u)⁻¹ · ∫_u^v haz(r) · (E[Δg](r) − comp(r)) dr`,   `u = s − T_N`, `v = t − T_N`.

Three ingredients meet here.

*Pathwise reduction.*  Once the segment has started, "the segment has ended by
`t`" is "the holding time is at most the age `v`", so the completed part is the
realized centered reset carried on the age window `(u, v]`.  Since the age
window has the deterministic length `t − s`, it is a window of the form
`(u, u+T]`.

*The channel step.*  Conditionally on the history and the realized holding
time, the realized reset increment averages to the normalized expected reset
increment at the pre-jump state; this replaces the realized reset by the
deterministic profile `E[Δg]` evaluated at the realized age.

*The density step.*  The realized age of a Lipschitz profile integrates, over
the window, to the hazard average of that profile — the density form of the
conditional holding-time law.

The result is `∫_B ∫_u^{u+T} haz·(E[Δg] − comp)`, and the weighted survivor
identity turns the conditional completed mean on the survival event into the
same quantity.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-- The centered reset profile of a segment: the normalized expected reset
increment at the state reached after flowing for the given age, minus the
partial occupation compensator at that age. -/
def davisSegmentCenteredResetProfile (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (g : DavisState Q n → ℝ) (z : DavisState Q n) (r : ℝ) : ℝ :=
  davisExpectedResetIncrement S g (davisFlow S hflow r.toNNReal z) -
    davisSegmentResetOccupationCompensator S hflow g z r.toNNReal

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The conditional completed mean is the hazard average of the centered reset
profile over the age window, renormalized by the survivor factor. -/
theorem davisSegmentConditionalCompletedMean_eq_windowIntegral
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) (u T : ℝ≥0) :
    davisSegmentConditionalCompletedMean S hflow g z u (u + T) =
      (davisSegmentSurvivor S hflow z u)⁻¹ *
        davisHazardWindowIntegral S hflow
          (davisSegmentCenteredResetProfile S hflow g) z u T := rfl

set_option maxHeartbeats 4000000 in
/-- **The conditional law of the completed part on a history survival event.**
On the part of a pre-jump history event at index `N` on which segment `N` is
still running at `s`, the mean of the completed part at a later time `t` is the
mean of the conditional completed mean. -/
theorem DavisJumpNoise.setIntegral_segmentCompletedPart
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
    (N : ℕ) (s t : ℝ≥0) (hst : s ≤ t) (hRmax : ((t : ℝ≥0) : ℝ) ≤ Rmax)
    (B : Set Ω)
    (hB : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N] B)
    (hBstart : ∀ ω ∈ B, ξ.jumpTime N ω ≤ s) :
    ∫ ω in B ∩ {ω | s - ξ.jumpTime N ω < ξ.holdingTime N ω},
        davisSegmentCompletedPart S hflow ξ initial g N t ω ∂P =
      ∫ ω in B ∩ {ω | s - ξ.jumpTime N ω < ξ.holdingTime N ω},
        davisSegmentConditionalCompletedMean S hflow g
          (davisStateAfterJump S hflow ξ initial N ω)
          (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω) ∂P := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  have hm : (F N : MeasurableSpace Ω) ≤ mΩ := F.le N
  have hBm : MeasurableSet B := hm _ hB
  set Phi : DavisState Q n → ℝ → ℝ :=
    davisSegmentCenteredResetProfile S hflow g with hPhi
  set zz : Ω → DavisState Q n :=
    fun ω => davisStateAfterJump S hflow ξ initial N ω with hzz
  set uu : Ω → ℝ≥0 := fun ω => s - ξ.jumpTime N ω with huu
  set vv : Ω → ℝ≥0 := fun ω => t - ξ.jumpTime N ω with hvv
  set T : ℝ≥0 := t - s with hT
  set hh : Ω → ℝ≥0 := ξ.holdingTime N with hhh
  have hhm : Measurable hh := hξ.holdingTime N
  have hTmeas : Measurable[F N] (ξ.jumpTime N) :=
    ξ.measurable_jumpTime_preJumpHistory S hflow hf hr hξ initial N
  have humeas : Measurable[F N] uu := measurable_const.sub hTmeas
  have hzF : Measurable[F N] zz :=
    (DavisPreJumpHistory.measurable_currentState N).comp
      (ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial N)
  have hzm : Measurable zz := hzF.mono hm le_rfl
  have hum : Measurable uu := humeas.mono hm le_rfl
  have hK0 : 0 ≤ K :=
    le_trans (abs_nonneg _) (hK initial 0 (le_trans t.coe_nonneg hRmax))
  -- every age involved lies below the horizon
  have hage : ∀ ω, ((uu ω + T : ℝ≥0) : ℝ) ≤ Rmax := by
    intro ω
    refine le_trans ?_ hRmax
    have hus : uu ω ≤ s := tsub_le_self
    have hle : uu ω + T ≤ t := by
      calc uu ω + T ≤ s + T := by gcongr
        _ = t := add_tsub_cancel_of_le hst
    exact_mod_cast hle
  -- the age window has deterministic length on `B`
  have hvT : ∀ ω ∈ B, vv ω = uu ω + T := by
    intro ω hω
    have h1 : ξ.jumpTime N ω ≤ s := hBstart ω hω
    show t - ξ.jumpTime N ω = (s - ξ.jumpTime N ω) + (t - s)
    rw [add_comm]
    exact (tsub_add_tsub_cancel hst h1).symm
  -- measurable sets
  have hSum : MeasurableSet {ω | uu ω < hh ω} := measurableSet_lt hum hhm
  have hWm : MeasurableSet {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T} := by
    have hEq : {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T} =
        {ω | uu ω < hh ω} \ {ω | uu ω + T < hh ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]
    exact hEq ▸ hSum.diff (measurableSet_lt (hum.add measurable_const) hhm)
  -- Step 1: the completed part is the realized centered reset on the window
  have hstep1 : ∫ ω in B ∩ {ω | uu ω < hh ω},
        davisSegmentCompletedPart S hflow ξ initial g N t ω ∂P =
      ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
        (davisRealizedResetIncrement S hflow ξ initial g N ω -
          davisSampledResetOccupationCompensator S hflow g ξ initial N ω) ∂P := by
    have hpt : ∀ ω ∈ B ∩ {ω | uu ω < hh ω},
        davisSegmentCompletedPart S hflow ξ initial g N t ω =
          {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T}.indicator
            (fun ω => davisRealizedResetIncrement S hflow ξ initial g N ω -
              davisSampledResetOccupationCompensator S hflow g ξ initial N ω)
            ω := by
      rintro ω ⟨hωB, hωS⟩
      have hstart : ξ.jumpTime N ω ≤ t := le_trans (hBstart ω hωB) hst
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
      · have hmem : ω ∈ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T} := by
          refine ⟨hωS, ?_⟩
          rw [← hvT ω hωB]
          exact hiff.1 hend
        rw [if_pos hend, Set.indicator_of_mem hmem]
      · have hnot : ω ∉ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T} := by
          intro hmem
          refine hend (hiff.2 ?_)
          rw [hvT ω hωB]
          exact hmem.2
        rw [if_neg hend, Set.indicator_of_notMem hnot]
    have hsets : (B ∩ {ω | uu ω < hh ω}) ∩
        {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T} =
        B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T} := by
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
      (B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T}) := by
    have hBpre : MeasurableSet[ξ.preChannelSpace S hflow initial N] B :=
      (ξ.preJumpHistorySpace_le_preChannel S hflow initial N) B hB
    have hupre : Measurable[ξ.preChannelSpace S hflow initial N] uu :=
      humeas.mono (ξ.preJumpHistorySpace_le_preChannel S hflow initial N) le_rfl
    have hhpre : Measurable[ξ.preChannelSpace S hflow initial N] hh :=
      DavisJumpNoise.holdingTime_measurable_preChannel S hflow ξ initial N
    have hEq : {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T} =
        {ω | uu ω < hh ω} \ {ω | uu ω + T < hh ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_diff, not_lt]
    refine hBpre.inter ?_
    rw [hEq]
    exact (measurableSet_lt hupre hhpre).diff
      (measurableSet_lt (hupre.add measurable_const) hhpre)
  have hstep2 : ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
        davisRealizedResetIncrement S hflow ξ initial g N ω ∂P =
      ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
        davisExpectedResetIncrement S g
          (davisStateBeforeJump S hflow ξ initial N ω) ∂P := by
    have h := hchan.setIntegral_realizedResetIncrement_weighted hf hr hξ g hg
      Cg hgC N (B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T}) hpreChan
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
  have hstep3 : ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
        Phi (zz ω) ((hh ω : ℝ≥0) : ℝ) ∂P =
      ∫ ω in B, davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) T ∂P :=
    hlaw.setIntegral_holdingTime_density_of_age_le hcont hsurv Phi hPhimeas
      hPhicont L hL hlip Rmax K hK N uu humeas T B hB (fun ω _ => hage ω)
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
  have hCbound : ∀ ω ∈ B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
      |davisSampledResetOccupationCompensator S hflow g ξ
      initial N ω| ≤ 2 * Cg + K := by
    intro ω hωD
    have hhle : ((hh ω : ℝ≥0) : ℝ) ≤ Rmax := by
      refine le_trans ?_ (hage ω)
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
  have hwinmeasF : Measurable[F N] fun ω =>
      davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) T :=
    (measurable_davisHazardWindowIntegral S hflow hf hsurv Phi hPhimeas T).comp
      (hzF.prodMk humeas)
  have hsurUF : Measurable[F N] fun ω =>
      davisSegmentSurvivor S hflow (zz ω) (uu ω) :=
    hsurv.comp (hzF.prodMk humeas)
  set wgt : Ω → ℝ := fun ω =>
    (davisSegmentSurvivor S hflow (zz ω) (uu ω))⁻¹ *
      davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) T with hwgt
  have hwgtF : Measurable[F N] wgt := (hsurUF.inv).mul hwinmeasF
  have hwgtK : ∀ ω, |wgt ω| ≤ K := by
    intro ω
    have hpos : 0 < davisSegmentSurvivor S hflow (zz ω) (uu ω) :=
      davisSegmentSurvivor_pos S hflow (zz ω) (uu ω)
    have hb := abs_davisHazardWindowIntegral_le_mul_survivor_sub_of_age_le S
      hflow hcont Phi hPhicont hK (zz ω) (uu ω) T (hage ω)
    have hposv : 0 < davisSegmentSurvivor S hflow (zz ω) (uu ω + T) :=
      davisSegmentSurvivor_pos S hflow (zz ω) (uu ω + T)
    rw [hwgt, abs_mul, abs_of_pos (inv_pos.2 hpos)]
    have hK1 : |davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) T| ≤
        K * davisSegmentSurvivor S hflow (zz ω) (uu ω) := by
      refine le_trans hb ?_
      have hle : davisSegmentSurvivor S hflow (zz ω) (uu ω) -
          davisSegmentSurvivor S hflow (zz ω) (uu ω + T) ≤
          davisSegmentSurvivor S hflow (zz ω) (uu ω) := by linarith
      exact mul_le_mul_of_nonneg_left hle hK0
    calc (davisSegmentSurvivor S hflow (zz ω) (uu ω))⁻¹ *
          |davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) T|
        ≤ (davisSegmentSurvivor S hflow (zz ω) (uu ω))⁻¹ *
            (K * davisSegmentSurvivor S hflow (zz ω) (uu ω)) :=
          mul_le_mul_of_nonneg_left hK1 (le_of_lt (inv_pos.2 hpos))
      _ = K := by field_simp
  have hstep4 : ∫ ω in B ∩ {ω | uu ω < hh ω}, wgt ω ∂P =
      ∫ ω in B, davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) T ∂P := by
    have h := hlaw.setIntegral_lt_holdingTime_weighted hcont hsurv N uu humeas
      B hB wgt hwgtF K hwgtK
    rw [h]
    refine setIntegral_congr_fun hBm fun ω _ => ?_
    have hpos : davisSegmentSurvivor S hflow (zz ω) (uu ω) ≠ 0 :=
      ne_of_gt (davisSegmentSurvivor_pos S hflow (zz ω) (uu ω))
    show wgt ω * davisSegmentSurvivor S hflow (zz ω) (uu ω) = _
    rw [hwgt]
    field_simp
  -- assemble the left-hand side
  have hLHS : ∫ ω in B ∩ {ω | uu ω < hh ω},
      davisSegmentCompletedPart S hflow ξ initial g N t ω ∂P =
      ∫ ω in B, davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) T ∂P := by
    rw [hstep1]
    have hsplit : ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
        (davisRealizedResetIncrement S hflow ξ initial g N ω -
          davisSampledResetOccupationCompensator S hflow g ξ initial N ω) ∂P =
        (∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
            davisRealizedResetIncrement S hflow ξ initial g N ω ∂P) -
          ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
            davisSampledResetOccupationCompensator S hflow g ξ initial N ω
              ∂P :=
      integral_sub (hboundint _ hDm (2 * Cg) hDbound _)
        (hboundintOn _ hCm (2 * Cg + K) _ (hBm.inter hWm) hCbound)
    have hjoin : (∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
          davisExpectedResetIncrement S g
            (davisStateBeforeJump S hflow ξ initial N ω) ∂P) -
        (∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
          davisSampledResetOccupationCompensator S hflow g ξ initial N ω ∂P) =
        ∫ ω in B ∩ {ω | uu ω < hh ω ∧ hh ω ≤ uu ω + T},
          Phi (zz ω) ((hh ω : ℝ≥0) : ℝ) ∂P := by
      rw [← integral_sub (hboundint _ hEm (2 * Cg) (fun ω => hEbound _) _)
        (hboundintOn _ hCm (2 * Cg + K) _ (hBm.inter hWm) hCbound)]
      exact setIntegral_congr_fun (hBm.inter hWm) fun ω _ => hprofile ω
    rw [hsplit, hstep2, hjoin, hstep3]
  -- assemble the right-hand side
  have hRHS : ∫ ω in B ∩ {ω | uu ω < hh ω},
      davisSegmentConditionalCompletedMean S hflow g (zz ω) (uu ω) (vv ω) ∂P =
      ∫ ω in B, davisHazardWindowIntegral S hflow Phi (zz ω) (uu ω) T ∂P := by
    rw [← hstep4]
    refine setIntegral_congr_fun (hBm.inter hSum) fun ω hω => ?_
    rw [hvT ω hω.1,
      davisSegmentConditionalCompletedMean_eq_windowIntegral S hflow g
        (zz ω) (uu ω) T]
  rw [hLHS, hRHS]

end SHS
