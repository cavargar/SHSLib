import SHSLib.Core.DavisSegmentConditionalRandomWindow
import SHSLib.Core.DavisFiniteCompensatorBounds

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Centering of a segment observed from its start

The conditional step law of the one-segment martingale has a third field
besides the two conditional laws: a segment that has **not yet started** at the
observation time carries, at every later time, a centered contribution.  Unlike
the other two fields, this one conditions at the random time at which the
segment starts, so it is not a statement about a fixed age.

The route taken here removes the randomness of the observation time altogether.
A segment that has not started at `s` is entirely determined by the history
before its own jump index, so it suffices to prove the stronger statement

`∫_B (contribution of segment N at time t) = 0`  for **every** pre-jump history
event `B` at index `N`,

with no reference to an observation time at all.  Its proof is the previous
module at the start age `u = 0`:

* on the event that the segment has not started by `t` the contribution
  vanishes pointwise, so the integral may be restricted to the history event on
  which it has started;
* there the age window of the completed part is `(0, V]` with the
  history-measurable length `V = t − T_N`, and the two laws of the previous
  module evaluate the two parts by the two conditional means at start age `0`;
* the deterministic core of the conditional step evaluates their difference as
  `−comp(0) = 0`;
* finally the survival event `{0 < h_N}` carries full probability, because the
  survivor factor at age `0` is `1`, so restricting to it changes no integral.

The last point is recorded separately: under the conditional holding-time law
no segment has a vanishing holding time.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Two elementary facts -/

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- The partial occupation compensator vanishes at age zero. -/
@[simp] theorem davisSegmentResetOccupationCompensator_zero_age
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) (g : DavisState Q n → ℝ)
    (z : DavisState Q n) :
    davisSegmentResetOccupationCompensator S hflow g z 0 = 0 := by
  unfold davisSegmentResetOccupationCompensator
  simp

/-- **The deterministic core at start age zero.**  Observed from the start of a
segment, the conditional means of the completed and of the active part
coincide. -/
theorem davisSegmentConditionalMean_sub_zero
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (g : DavisState Q n → ℝ)
    (hgcont : DavisResetOccupationContinuousAlongFlow S hflow g)
    (z : DavisState Q n) (v : ℝ≥0) :
    davisSegmentConditionalCompletedMean S hflow g z 0 v =
      davisSegmentConditionalActiveMean S hflow g z 0 v := by
  have h := davisSegmentConditionalMean_sub S hflow hcont g hgcont z 0 v
    (zero_le v)
  rw [davisSegmentResetOccupationCompensator_zero_age S hflow g z, neg_zero]
    at h
  linarith

/-! ## No segment has a vanishing holding time -/

/-- Under the conditional holding-time law, the holding time of every segment
is almost surely positive: the survivor factor at age zero is one. -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.measure_holdingTime_eq_zero
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial) (k : ℕ) :
    P {ω | ξ.holdingTime k ω = 0} = 0 := by
  have hpos : MeasurableSet {ω | 0 < ξ.holdingTime k ω} :=
    measurableSet_lt measurable_const (hξ.holdingTime k)
  have hfull : P {ω | 0 < ξ.holdingTime k ω} = P Set.univ := by
    have h := hlaw.measure_holdingTime_gt k 0
    have hone : ∀ ω : Ω, ENNReal.ofReal
        ((davisPreJumpHistory S hflow ξ initial k ω).nextSurvivor S hflow 0)
        = 1 := by
      intro ω
      rw [DavisPreJumpHistory.nextSurvivor,
        davisSegmentSurvivor_zero S hflow _]
      simp
    rw [h]
    simp only [hone]
    simp
  have hcompl : {ω | ξ.holdingTime k ω = 0} = {ω | 0 < ξ.holdingTime k ω}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt, le_zero_iff]
  rw [hcompl, measure_compl hpos (measure_ne_top P _), hfull, tsub_self]

/-! ## The centering of a single segment on a history event -/

set_option maxHeartbeats 4000000 in
/-- **Centering of a segment contribution on a pre-jump history event.**  For
every event determined by the history before jump `N`, the contribution of
segment `N` at any elapsed time has vanishing mean. -/
theorem DavisJumpNoise.setIntegral_segmentContribution_preJumpHistory_eq_zero
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
    (Rmax K : ℝ) (hK : ∀ z r, r ≤ Rmax →
      |davisSegmentCenteredResetProfile S hflow g z r| ≤ K)
    (N : ℕ) (t : ℝ≥0) (hRmax : ((t : ℝ≥0) : ℝ) ≤ Rmax) (B : Set Ω)
    (hB : MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N]
      B) :
    ∫ ω in B, davisElapsedOccupationSegmentContribution S hflow ξ hne initial
      g N t ω ∂P = 0 := by
  classical
  set F := ξ.preJumpHistoryFiltration S hflow hf hr hξ initial with hF
  have hm : (F N : MeasurableSpace Ω) ≤ mΩ := F.le N
  have hBm : MeasurableSet B := hm _ hB
  have hsurv : Measurable fun p : DavisState Q n × ℝ≥0 =>
      davisSegmentSurvivor S hflow p.1 p.2 := hreg.survivor_measurable
  have hRmax0 : (0 : ℝ) ≤ Rmax := le_trans t.coe_nonneg hRmax
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK initial 0 hRmax0)
  have hCg0 : 0 ≤ Cg := le_trans (abs_nonneg _) (hgC initial)
  -- the compensator inherits a bound from the profile, below the horizon
  have hcompbound : ∀ (z : DavisState Q n) (u : ℝ≥0), ((u : ℝ≥0) : ℝ) ≤ Rmax →
      |davisSegmentResetOccupationCompensator S hflow g z u| ≤ K + 2 * Cg := by
    intro z u hu
    have h := hK z ((u : ℝ≥0) : ℝ) hu
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
  -- the two parts and their bounds
  set zz : Ω → DavisState Q n :=
    fun ω => davisStateAfterJump S hflow ξ initial N ω with hzz
  set V : Ω → ℝ≥0 := fun ω => t - ξ.jumpTime N ω with hV
  have hTmeas : Measurable[F N] (ξ.jumpTime N) :=
    ξ.measurable_jumpTime_preJumpHistory S hflow hf hr hξ initial N
  have hVF : Measurable[F N] V := measurable_const.sub hTmeas
  have hVm : Measurable V := hVF.mono hm le_rfl
  have hzF : Measurable[F N] zz :=
    (DavisPreJumpHistory.measurable_currentState N).comp
      (ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial N)
  have hzm : Measurable zz := hzF.mono hm le_rfl
  have hVle : ∀ ω, V ω ≤ t := fun ω => tsub_le_self
  have hVR : ∀ ω, ((V ω : ℝ≥0) : ℝ) ≤ Rmax := fun ω =>
    le_trans (by exact_mod_cast hVle ω) hRmax
  -- integrability helper
  have hboundint : ∀ (f : Ω → ℝ), Measurable f → ∀ (c : ℝ), (∀ ω, |f ω| ≤ c) →
      ∀ D : Set Ω, IntegrableOn f D P := by
    intro f hfm c hfc D
    refine Integrable.integrableOn ?_
    refine (integrable_const (max c 0)).mono' hfm.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact le_trans (hfc ω) (le_max_left c 0)
  -- measurability of the two parts
  have hDm : Measurable (davisRealizedResetIncrement S hflow ξ initial g N) :=
    hξ.realizedResetIncrement S hflow hf hr initial g hg N
  have hSm : Measurable
      (davisSampledResetOccupationCompensator S hflow g ξ initial N) :=
    hreg.stoppedCompensator_measurable.comp
      (hzm.prodMk (hξ.holdingTime N))
  have hjumpm : ∀ k : ℕ, Measurable (ξ.jumpTime k) := fun k => hξ.jumpTime k
  have hcompletedm : Measurable
      (davisSegmentCompletedPart S hflow ξ initial g N t) := by
    unfold davisSegmentCompletedPart davisSegmentCompletedContribution
    exact Measurable.ite (measurableSet_le (hjumpm (N + 1)) measurable_const)
      (hDm.sub hSm) measurable_const
  have hactivem : Measurable
      (davisSegmentActivePart S hflow ξ initial g N t) := by
    unfold davisSegmentActivePart
    refine Measurable.ite (measurableSet_le (hjumpm (N + 1)) measurable_const)
      measurable_const ?_
    exact Measurable.ite (measurableSet_le (hjumpm N) measurable_const)
      (hreg.stoppedCompensator_measurable.comp (hzm.prodMk hVm))
      measurable_const
  -- on the event that the segment has ended by `t` its holding time is below
  -- the horizon
  have hSbound : ∀ ω, ξ.jumpTime (N + 1) ω ≤ t →
      |davisSampledResetOccupationCompensator S hflow g ξ initial N ω| ≤
        K + 2 * Cg := by
    intro ω hend
    have hle : ξ.holdingTime N ω ≤ t := by
      have h := hend
      rw [DavisJumpNoise.jumpTime_succ] at h
      exact le_trans le_add_self h
    exact hcompbound _ _ (le_trans (by exact_mod_cast hle) hRmax)
  have hcompletedb : ∀ ω,
      |davisSegmentCompletedPart S hflow ξ initial g N t ω| ≤
        2 * Cg + (K + 2 * Cg) := by
    intro ω
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
              Cg hgC N ω) (hSbound ω hend)
    · rw [if_neg hend, abs_zero]
      positivity
  have hactiveb : ∀ ω,
      |davisSegmentActivePart S hflow ξ initial g N t ω| ≤ K + 2 * Cg := by
    intro ω
    unfold davisSegmentActivePart
    by_cases hend : ξ.jumpTime (N + 1) ω ≤ t
    · rw [if_pos hend, abs_zero]; positivity
    · rw [if_neg hend]
      by_cases hstart : ξ.jumpTime N ω ≤ t
      · rw [if_pos hstart]; exact hcompbound _ _ (hVR ω)
      · rw [if_neg hstart, abs_zero]; positivity
  -- restrict to the event that the segment has started
  set B₁ : Set Ω := B ∩ {ω | ξ.jumpTime N ω ≤ t} with hB₁
  have hB₁F : MeasurableSet[F N] B₁ :=
    hB.inter (measurableSet_le hTmeas measurable_const)
  have hB₁m : MeasurableSet B₁ := hm _ hB₁F
  have hrestrict : ∫ ω in B, davisElapsedOccupationSegmentContribution S hflow
      ξ hne initial g N t ω ∂P =
      ∫ ω in B₁, davisElapsedOccupationSegmentContribution S hflow ξ hne
        initial g N t ω ∂P := by
    have hcm : Measurable (davisElapsedOccupationSegmentContribution S hflow ξ
        hne initial g N t) := by
      have heq : davisElapsedOccupationSegmentContribution S hflow ξ hne
          initial g N t = fun ω =>
            davisSegmentCompletedPart S hflow ξ initial g N t ω -
              davisSegmentActivePart S hflow ξ initial g N t ω := by
        funext ω
        exact davisElapsedOccupationSegmentContribution_eq_sub S hflow ξ hne
          initial g N t ω
      rw [heq]
      exact hcompletedm.sub hactivem
    have hsplit : B = B₁ ∪ (B \ {ω | ξ.jumpTime N ω ≤ t}) := by
      ext ω
      by_cases hω : ξ.jumpTime N ω ≤ t <;> simp [hB₁]
    have hdisj : Disjoint B₁ (B \ {ω | ξ.jumpTime N ω ≤ t}) := by
      rw [Set.disjoint_left]
      rintro ω ⟨-, hω⟩ ⟨-, hω'⟩
      exact hω' hω
    have hzero : ∫ ω in B \ {ω | ξ.jumpTime N ω ≤ t},
        davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N t ω
          ∂P = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun ω hω => ?_
      exact davisElapsedOccupationSegmentContribution_eq_zero_of_fresh S hflow
        ξ hne initial g N t ω hω.2
    rw [hsplit, setIntegral_union hdisj (hBm.diff
      (measurableSet_le (hjumpm N) measurable_const))
      ((hboundint _ hcm (2 * Cg + (K + 2 * Cg) + (K + 2 * Cg)) (fun ω => by
        rw [davisElapsedOccupationSegmentContribution_eq_sub]
        exact le_trans (abs_sub _ _)
          (add_le_add (hcompletedb ω) (hactiveb ω))) _))
      ((hboundint _ hcm (2 * Cg + (K + 2 * Cg) + (K + 2 * Cg)) (fun ω => by
        rw [davisElapsedOccupationSegmentContribution_eq_sub]
        exact le_trans (abs_sub _ _)
          (add_le_add (hcompletedb ω) (hactiveb ω))) _)), hzero, add_zero]
  -- the survival event at age zero carries full probability
  set S0 : Set Ω := {ω | (0 : ℝ≥0) < ξ.holdingTime N ω} with hS0
  have hS0m : MeasurableSet S0 :=
    measurableSet_lt measurable_const (hξ.holdingTime N)
  have hnull : P {ω | ξ.holdingTime N ω = 0} = 0 :=
    hlaw.measure_holdingTime_eq_zero N
  have hae : (B₁ ∩ S0 : Set Ω) =ᵐ[P] B₁ := by
    have hsub : B₁ \ (B₁ ∩ S0) ⊆ {ω | ξ.holdingTime N ω = 0} := by
      rintro ω ⟨hωB, hωn⟩
      by_contra hω
      exact hωn ⟨hωB, lt_of_le_of_ne (zero_le _) (Ne.symm hω)⟩
    have h1 : P (B₁ \ (B₁ ∩ S0)) = 0 :=
      measure_mono_null hsub hnull
    have h2 : P ((B₁ ∩ S0) \ B₁) = 0 := by
      have : (B₁ ∩ S0) \ B₁ = ∅ := by
        ext ω; simp +contextual
      rw [this, measure_empty]
    rw [MeasureTheory.ae_eq_set]
    exact ⟨h2, h1⟩
  -- the two conditional laws at start age zero
  have hlawC := hξ.holdingTime N
  have hcompleted := DavisJumpNoise.setIntegral_segmentCompletedPart_startAge
    hlaw hchan hcont hsurv hg Cg hgC hPhimeas hPhicont L hL hlip Rmax K hK N t
    hRmax (fun _ => (0 : ℝ≥0)) V measurable_const hVF t hVle B₁ hB₁F
    (fun ω hω => hω.2) (fun ω _ => by rw [hV]; exact (zero_add _).symm)
  have hactive := hlaw.setIntegral_segmentActivePart_startAge hcont hreg N t
    (fun _ => (0 : ℝ≥0)) measurable_const (fun ω => zero_le _) B₁ hB₁F
    (fun ω hω => hω.2) (K + 2 * Cg) (fun ω => hcompbound _ _ (hVR ω))
  -- the two conditional means agree pointwise at start age zero
  have hmeanC : Measurable fun ω => davisSegmentConditionalCompletedMean S hflow
      g (zz ω) 0 (V ω) := by
    have heq : (fun ω => davisSegmentConditionalCompletedMean S hflow g (zz ω)
        0 (V ω)) = fun ω =>
          (davisSegmentSurvivor S hflow (zz ω) 0)⁻¹ *
            davisHazardWindowIntegral S hflow
              (davisSegmentCenteredResetProfile S hflow g) (zz ω) 0 (V ω) := by
      funext ω
      have := davisSegmentConditionalCompletedMean_eq_windowIntegral S hflow g
        (zz ω) 0 (V ω)
      rw [zero_add] at this
      exact this
    rw [heq]
    exact ((hsurv.comp (hzm.prodMk measurable_const)).inv).mul
      ((measurable_davisHazardWindowIntegral_triple S hflow hf hsurv _
        hPhimeas).comp ((hzm.prodMk measurable_const).prodMk hVm))
  have hmeanA : Measurable fun ω => davisSegmentConditionalActiveMean S hflow g
      (zz ω) 0 (V ω) := by
    unfold davisSegmentConditionalActiveMean
    exact (((hsurv.comp (hzm.prodMk measurable_const)).inv).mul
      (hsurv.comp (hzm.prodMk hVm))).mul
      (hreg.stoppedCompensator_measurable.comp (hzm.prodMk hVm))
  have hmeanCb : ∀ ω, |davisSegmentConditionalCompletedMean S hflow g (zz ω) 0
      (V ω)| ≤ K := by
    intro ω
    have heq := davisSegmentConditionalCompletedMean_eq_windowIntegral S hflow g
      (zz ω) 0 (V ω)
    rw [zero_add] at heq
    rw [heq, davisSegmentSurvivor_zero, inv_one, one_mul]
    exact abs_davisHazardWindowIntegral_le_of_age_le S hflow hcont _ hPhicont
      hK (zz ω) 0 (V ω) (by simpa using hVR ω)
  have hmeanAb : ∀ ω, |davisSegmentConditionalActiveMean S hflow g (zz ω) 0
      (V ω)| ≤ K + 2 * Cg := by
    intro ω
    unfold davisSegmentConditionalActiveMean
    rw [davisSegmentSurvivor_zero, inv_one, one_mul, abs_mul]
    have h1 : |davisSegmentSurvivor S hflow (zz ω) (V ω)| ≤ 1 := by
      rw [abs_of_pos (davisSegmentSurvivor_pos S hflow (zz ω) (V ω))]
      exact davisSegmentSurvivor_le_one S hflow (zz ω) (V ω)
    calc |davisSegmentSurvivor S hflow (zz ω) (V ω)| *
          |davisSegmentResetOccupationCompensator S hflow g (zz ω) (V ω)|
        ≤ 1 * (K + 2 * Cg) :=
          mul_le_mul h1 (hcompbound _ _ (hVR ω)) (abs_nonneg _) zero_le_one
      _ = K + 2 * Cg := one_mul _
  -- assemble
  have hdiffzero : ∫ ω in B₁ ∩ S0,
      davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N t ω
        ∂P = 0 := by
    have hpt : ∀ ω, davisElapsedOccupationSegmentContribution S hflow ξ hne
        initial g N t ω =
          davisSegmentCompletedPart S hflow ξ initial g N t ω -
            davisSegmentActivePart S hflow ξ initial g N t ω := fun ω =>
      davisElapsedOccupationSegmentContribution_eq_sub S hflow ξ hne initial g
        N t ω
    have hsplit : ∫ ω in B₁ ∩ S0,
        davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N t ω
          ∂P =
        (∫ ω in B₁ ∩ S0, davisSegmentCompletedPart S hflow ξ initial g N t ω
            ∂P) -
          ∫ ω in B₁ ∩ S0, davisSegmentActivePart S hflow ξ initial g N t ω
            ∂P := by
      simp_rw [hpt]
      exact integral_sub
        (hboundint _ hcompletedm (2 * Cg + (K + 2 * Cg)) hcompletedb _)
        (hboundint _ hactivem (K + 2 * Cg) hactiveb _)
    have hcompleted' : ∫ ω in B₁ ∩ S0,
        davisSegmentCompletedPart S hflow ξ initial g N t ω ∂P =
        ∫ ω in B₁ ∩ S0, davisSegmentConditionalCompletedMean S hflow g
          (zz ω) 0 (V ω) ∂P := hcompleted
    have hactive' : ∫ ω in B₁ ∩ S0,
        davisSegmentActivePart S hflow ξ initial g N t ω ∂P =
        ∫ ω in B₁ ∩ S0, davisSegmentConditionalActiveMean S hflow g
          (zz ω) 0 (V ω) ∂P := hactive
    rw [hsplit, hcompleted', hactive']
    have hmeans : ∫ ω in B₁ ∩ S0, davisSegmentConditionalCompletedMean S hflow g
          (zz ω) 0 (V ω) ∂P -
        ∫ ω in B₁ ∩ S0, davisSegmentConditionalActiveMean S hflow g (zz ω) 0
          (V ω) ∂P =
        ∫ ω in B₁ ∩ S0, (davisSegmentConditionalCompletedMean S hflow g (zz ω)
          0 (V ω) - davisSegmentConditionalActiveMean S hflow g (zz ω) 0
            (V ω)) ∂P :=
      (integral_sub (hboundint _ hmeanC K hmeanCb _)
        (hboundint _ hmeanA (K + 2 * Cg) hmeanAb _)).symm
    rw [hmeans]
    have : ∀ ω, davisSegmentConditionalCompletedMean S hflow g (zz ω) 0 (V ω) -
        davisSegmentConditionalActiveMean S hflow g (zz ω) 0 (V ω) = 0 := by
      intro ω
      rw [davisSegmentConditionalMean_sub_zero S hflow hcont g hgcont (zz ω)
        (V ω), sub_self]
    simp_rw [this]
    simp
  rw [hrestrict, ← MeasureTheory.setIntegral_congr_set hae, hdiffzero]

end SHS
