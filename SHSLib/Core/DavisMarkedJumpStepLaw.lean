import SHSLib.Core.DavisMarkedJumpFiltration
import SHSLib.Core.DavisSegmentFreshCentering

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # The conditional step law for the marked jump filtration

The conditional laws of the segment theory are statements about the events of
the discrete pre-jump history filtration; the conditional step law of the
one-segment martingale asks for the same identities on the events of a
continuous-time filtration.  This module bridges the two for the observation
filtration of the marked jump history, by *representing* its events.

Two representations are proved.

* An event observable at `s` and contained in the event that segment `N` is
  active at `s` is, by the very definition of observability, the trace on that
  event of a pre-jump history event at index `N` on which the segment has
  started — that is, `B ∩ {s − T_N < h_N}`.  This is exactly the shape the two
  conditional laws of the completed and of the active part are proved for.

* An event observable at `s` and contained in the event that segment `N` has
  *not* started at `s` is itself a pre-jump history event at index `N`: it is
  the union, over the finitely many indices `k < N`, of the traces of the event
  on the events that segment `k` is active at `s`, each of which is a pre-jump
  history event at index `k+1 ≤ N`.  This is the shape the centering of a fresh
  segment is proved for.

With the two representations, the three integral identities of the conditional
step law hold verbatim for the marked jump filtration.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Representation of the observable events -/

/-- **Representation on an active event.**  An event observable at `s` on which
segment `N` is active is the survival part of a pre-jump history event at
index `N`. -/
theorem DavisJumpNoise.exists_preJumpHistory_of_subset_activeEvent
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (N : ℕ) (s : ℝ≥0)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.markedJumpSpace S hflow hf hr hξ initial s] A)
    (hAsub : A ⊆ ξ.activeEvent N s) :
    ∃ B : Set Ω,
      MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N] B ∧
        (∀ ω ∈ B, ξ.jumpTime N ω ≤ s) ∧
        A = B ∩ {ω | s - ξ.jumpTime N ω < ξ.holdingTime N ω} := by
  obtain ⟨B, hBmeas, hBstart, hBeq⟩ := hA N
  refine ⟨B, hBmeas, hBstart, ?_⟩
  have hAeq : A = B ∩ ξ.activeEvent N s := by
    rw [← hBeq]
    exact (Set.inter_eq_self_of_subset_left hAsub).symm
  rw [hAeq]
  ext ω
  constructor
  · rintro ⟨hωB, hωact⟩
    exact ⟨hωB, (davisSegmentActive_iff_age_lt_holdingTime ξ N s ω
      hωact.1).1 hωact.2⟩
  · rintro ⟨hωB, hωlt⟩
    refine ⟨hωB, hBstart ω hωB, ?_⟩
    exact (davisSegmentActive_iff_age_lt_holdingTime ξ N s ω
      (hBstart ω hωB)).2 hωlt

/-- **Representation on a fresh event.**  An event observable at `s` on which
segment `N` has not started is an event of the pre-jump history at index
`N`. -/
theorem DavisJumpNoise.measurableSet_preJumpHistory_of_subset_not_started
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (N : ℕ) (s : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[ξ.markedJumpSpace S hflow hf hr hξ initial s] A)
    (hAsub : A ⊆ {ω | ¬ ξ.jumpTime N ω ≤ s}) :
    MeasurableSet[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial N] A := by
  classical
  choose B hBmeas hBstart hBeq using hA
  have hAeq : A = ⋃ k : Fin N, (B (k : ℕ) ∩ ξ.activeEvent (k : ℕ) s) := by
    ext ω
    constructor
    · intro hωA
      set k := ξ.activeSegmentIndex hne s ω with hk
      have hactk : ω ∈ ξ.activeEvent k s :=
        ξ.mem_activeEvent_activeSegmentIndex hne s ω
      have hkN : k < N := by
        by_contra hcon
        push_neg at hcon
        exact hAsub hωA (le_trans (ξ.jumpTime_mono ω hcon) hactk.1)
      refine Set.mem_iUnion.mpr ⟨⟨k, hkN⟩, ?_⟩
      have hmem : ω ∈ A ∩ ξ.activeEvent k s := ⟨hωA, hactk⟩
      exact hBeq k ▸ hmem
    · intro hω
      obtain ⟨k, hωk⟩ := Set.mem_iUnion.mp hω
      have hmem : ω ∈ B (k : ℕ) ∩ ξ.activeEvent (k : ℕ) s := hωk
      exact ((hBeq (k : ℕ)).symm ▸ hmem :
        ω ∈ A ∩ ξ.activeEvent (k : ℕ) s).1
  rw [hAeq]
  refine MeasurableSet.iUnion fun k => MeasurableSet.inter ?_ ?_
  · exact (ξ.preJumpHistorySpace_mono S hflow initial (le_of_lt k.2)) _
      (hBmeas (k : ℕ))
  · exact ξ.measurableSet_activeEvent_preJumpHistory S hflow hf hr hξ initial
      (k : ℕ) N k.2 s

/-! ## The three integral identities of the conditional step law -/

/-- **The conditional law of the active part for the marked jump
filtration.** -/
theorem DavisJumpNoise.ConditionalHoldingTimeLaw.markedJump_active_conditional
    {S : SHS Q n m} {hflow : S.HasGlobalFlow}
    {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {ξ : DavisJumpNoise m Ω} {hξ : ξ.MeasurableNoise}
    {initial : DavisState Q n} {g : DavisState Q n → ℝ}
    (hlaw : ξ.ConditionalHoldingTimeLaw S hflow hf hr P hξ initial)
    (hcont : DavisHazardContinuousAlongFlow S hflow)
    (hreg : DavisResetOccupationRegular S hflow g)
    (N : ℕ) (s t : ℝ≥0) (hst : s ≤ t)
    (K : ℝ)
    (hK : ∀ ω, |davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial N ω)
      (t - ξ.jumpTime N ω)| ≤ K)
    (A : Set Ω)
    (hA : MeasurableSet[ξ.markedJumpSpace S hflow hf hr hξ initial s] A)
    (hAsub : A ⊆ {ω | ξ.jumpTime N ω ≤ s ∧ ¬ ξ.jumpTime (N + 1) ω ≤ s}) :
    ∫ ω in A, davisSegmentActivePart S hflow ξ initial g N t ω ∂P =
      ∫ ω in A, davisSegmentConditionalActiveMean S hflow g
        (davisStateAfterJump S hflow ξ initial N ω)
        (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω) ∂P := by
  obtain ⟨B, hBmeas, hBstart, hAeq⟩ :=
    ξ.exists_preJumpHistory_of_subset_activeEvent S hflow hf hr hξ initial N s
      A hA hAsub
  rw [hAeq]
  exact hlaw.setIntegral_segmentActivePart hcont hreg N s t hst B hBmeas
    hBstart K hK

/-- **The conditional law of the completed part for the marked jump
filtration.** -/
theorem DavisJumpNoise.markedJump_completed_conditional
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
    (A : Set Ω)
    (hA : MeasurableSet[ξ.markedJumpSpace S hflow hf hr hξ initial s] A)
    (hAsub : A ⊆ {ω | ξ.jumpTime N ω ≤ s ∧ ¬ ξ.jumpTime (N + 1) ω ≤ s}) :
    ∫ ω in A, davisSegmentCompletedPart S hflow ξ initial g N t ω ∂P =
      ∫ ω in A, davisSegmentConditionalCompletedMean S hflow g
        (davisStateAfterJump S hflow ξ initial N ω)
        (s - ξ.jumpTime N ω) (t - ξ.jumpTime N ω) ∂P := by
  obtain ⟨B, hBmeas, hBstart, hAeq⟩ :=
    ξ.exists_preJumpHistory_of_subset_activeEvent S hflow hf hr hξ initial N s
      A hA hAsub
  rw [hAeq]
  exact DavisJumpNoise.setIntegral_segmentCompletedPart hlaw hchan hcont hsurv
    hg Cg hgC hPhimeas hPhicont L hL hlip Rmax K hK N s t hst hRmax B hBmeas
    hBstart

/-- **Centering of a fresh segment for the marked jump filtration.** -/
theorem DavisJumpNoise.markedJump_fresh_centered
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
    (N : ℕ) (s t : ℝ≥0) (hRmax : ((t : ℝ≥0) : ℝ) ≤ Rmax) (A : Set Ω)
    (hA : MeasurableSet[ξ.markedJumpSpace S hflow hf hr hξ initial s] A)
    (hAsub : A ⊆ {ω | ¬ ξ.jumpTime N ω ≤ s}) :
    ∫ ω in A, davisElapsedOccupationSegmentContribution S hflow ξ hne initial
      g N t ω ∂P = 0 :=
  DavisJumpNoise.setIntegral_segmentContribution_preJumpHistory_eq_zero hne
    hlaw hchan hcont hgcont hreg hg Cg hgC hPhimeas hPhicont L hL hlip Rmax K hK
    N t hRmax
    A (ξ.measurableSet_preJumpHistory_of_subset_not_started S hflow hf hr hξ
      hne initial N s A hA hAsub)

end SHS
