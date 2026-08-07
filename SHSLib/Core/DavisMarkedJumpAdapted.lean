import SHSLib.Core.DavisMarkedJumpStepLaw

open MeasureTheory MeasurableSpace
open scoped ENNReal NNReal

noncomputable section

/-! # Observability of a segment contribution, and the step law in full

The three integral identities of the conditional step law hold for the
observation filtration of the marked jump history.  What is still missing
before the interface itself can be produced is its structural part: the
contribution of a segment must be observable at every time, cumulative jump
times must be observable, and the quantities involved must be integrable.

Observability is the substance of this module.  On the event that segment `M`
is the active one at time `t`, the contribution of segment `N` takes one of
three forms, according to whether `N` is before, equal to or after `M`: the
fully realized centered reset of a completed segment, minus the partial
occupation compensator of the running segment, or zero.  Each of these is a
function of the pre-jump history at index `M`, and this is precisely the
defining requirement of observability at time `t`.

The pre-jump history measurability of the first two forms is proved from
scratch here: the post-jump states, the holding times and the channel marks are
coordinates of the finite history, the pre-jump states are their images under
the flow, and a realized reset increment is the difference of the test function
at two such states — the state after the *next* jump and the state before it.

With observability in place, and with integrability supplied by the bound the
centered reset profile puts on the occupation compensator, the interface
`DavisSegmentConditionalStepLaw` is produced in full for the marked jump
filtration.  Through the results of the earlier modules this yields the
martingale property of a single flow segment, and hence the
deterministic-cap increment law, for a genuine observation filtration.
-/

namespace SHS

variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
  {n m : ℕ}

/-! ## Coordinates of a finite history -/

omit [MeasurableSingletonClass Q] in
/-- Each channel coordinate of a finite history is measurable. -/
theorem DavisPreJumpHistory.measurable_channel (k : ℕ) (i : Fin k) :
    Measurable fun H : DavisPreJumpHistory Q n m k => H.channel i := by
  have hencode : Measurable fun H : DavisPreJumpHistory Q n m k =>
      (H.holdingTime, H.channel, H.stateAfterJump) := by
    rw [measurable_iff_comap_le]
    rfl
  exact (measurable_pi_apply i).comp hencode.snd.fst

omit [MeasurableSingletonClass Q] in
/-- Each post-jump state coordinate of a finite history is measurable. -/
theorem DavisPreJumpHistory.measurable_stateAfterJump (k : ℕ) (i : Fin (k + 1)) :
    Measurable fun H : DavisPreJumpHistory Q n m k => H.stateAfterJump i := by
  have hencode : Measurable fun H : DavisPreJumpHistory Q n m k =>
      (H.holdingTime, H.channel, H.stateAfterJump) := by
    rw [measurable_iff_comap_le]
    rfl
  exact (measurable_pi_apply i).comp hencode.snd.snd

/-! ## Pre-jump history measurability of the segment quantities -/

variable {S : SHS Q n m} {hflow : S.HasGlobalFlow}
  {hf : DavisFlowRegular S hflow} {hr : DavisResetRegular S}

/-- Post-jump states at earlier indices are observable in the pre-jump
history. -/
theorem DavisJumpNoise.measurable_stateAfterJump_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (j k : ℕ)
    (hjk : j ≤ k) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (davisStateAfterJump S hflow ξ initial j) := by
  have hH := ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial k
  have heq : davisStateAfterJump S hflow ξ initial j = fun ω =>
      (davisPreJumpHistory S hflow ξ initial k ω).stateAfterJump
        ⟨j, Nat.lt_succ_of_le hjk⟩ := rfl
  rw [heq]
  exact (DavisPreJumpHistory.measurable_stateAfterJump k _).comp hH

/-- Holding times at earlier indices are observable in the pre-jump history. -/
theorem DavisJumpNoise.measurable_holdingTime_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (j k : ℕ)
    (hjk : j < k) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (ξ.holdingTime j) := by
  have hH := ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial k
  have heq : ξ.holdingTime j = fun ω =>
      (davisPreJumpHistory S hflow ξ initial k ω).holdingTime ⟨j, hjk⟩ := rfl
  rw [heq]
  exact (DavisPreJumpHistory.measurable_holdingTime k _).comp hH

/-- Channel marks at earlier indices are observable in the pre-jump history. -/
theorem DavisJumpNoise.measurable_channel_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (j k : ℕ)
    (hjk : j < k) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (ξ.channel j) := by
  have hH := ξ.preJumpHistory_measurable_filtration S hflow hf hr hξ initial k
  have heq : ξ.channel j = fun ω =>
      (davisPreJumpHistory S hflow ξ initial k ω).channel ⟨j, hjk⟩ := rfl
  rw [heq]
  exact (DavisPreJumpHistory.measurable_channel k _).comp hH

/-- Pre-jump states at earlier indices are observable in the pre-jump
history. -/
theorem DavisJumpNoise.measurable_stateBeforeJump_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (j k : ℕ)
    (hjk : j < k) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial k]
      (davisStateBeforeJump S hflow ξ initial j) := by
  have heq : davisStateBeforeJump S hflow ξ initial j = fun ω =>
      davisFlow S hflow (ξ.holdingTime j ω)
        (davisStateAfterJump S hflow ξ initial j ω) := rfl
  rw [heq]
  exact hf.measurable_joint.comp
    ((ξ.measurable_holdingTime_preJumpHistory S hflow hf hr hξ initial j k
        hjk).prodMk
      (ξ.measurable_stateAfterJump_preJumpHistory S hflow hf hr hξ initial j k
        (le_of_lt hjk)))

/-- A realized reset increment is observable in the pre-jump history one index
later: it is the test function at the state after the next jump minus the test
function at the state before it. -/
theorem DavisJumpNoise.measurable_realizedResetIncrement_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    (g : DavisState Q n → ℝ) (hg : Measurable g) (j : ℕ) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial (j + 1)]
      (davisRealizedResetIncrement S hflow ξ initial g j) := by
  have heq : davisRealizedResetIncrement S hflow ξ initial g j = fun ω =>
      g (davisStateAfterJump S hflow ξ initial (j + 1) ω) -
        g (davisStateBeforeJump S hflow ξ initial j ω) := by
    funext ω
    rw [davisRealizedResetIncrement, davisStateAfterJump_succ]
  rw [heq]
  exact (hg.comp (ξ.measurable_stateAfterJump_preJumpHistory S hflow hf hr hξ
      initial (j + 1) (j + 1) le_rfl)).sub
    (hg.comp (ξ.measurable_stateBeforeJump_preJumpHistory S hflow hf hr hξ
      initial j (j + 1) (Nat.lt_succ_self j)))

/-- The sampled occupation compensator of a segment is observable in the
pre-jump history one index later. -/
theorem DavisJumpNoise.measurable_sampledCompensator_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    {g : DavisState Q n → ℝ} (hreg : DavisResetOccupationRegular S hflow g)
    (j : ℕ) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial (j + 1)]
      (davisSampledResetOccupationCompensator S hflow g ξ initial j) := by
  have heq : davisSampledResetOccupationCompensator S hflow g ξ initial j =
      fun ω => davisSegmentResetOccupationCompensator S hflow g
        (davisStateAfterJump S hflow ξ initial j ω) (ξ.holdingTime j ω) := rfl
  rw [heq]
  exact hreg.stoppedCompensator_measurable.comp
    ((ξ.measurable_stateAfterJump_preJumpHistory S hflow hf hr hξ initial j
        (j + 1) (Nat.le_succ j)).prodMk
      (ξ.measurable_holdingTime_preJumpHistory S hflow hf hr hξ initial j
        (j + 1) (Nat.lt_succ_self j)))

/-- The completed contribution of a segment is observable in the pre-jump
history one index later. -/
theorem DavisJumpNoise.measurable_segmentCompletedContribution_preJumpHistory
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    {g : DavisState Q n → ℝ} (hg : Measurable g)
    (hreg : DavisResetOccupationRegular S hflow g) (j : ℕ) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial (j + 1)]
      (davisSegmentCompletedContribution S hflow ξ initial g j) :=
  (ξ.measurable_realizedResetIncrement_preJumpHistory S hflow hf hr hξ initial
      g hg j).sub
    (ξ.measurable_sampledCompensator_preJumpHistory S hflow hf hr hξ initial
      hreg j)

/-! ## The history form of a segment contribution -/

/-- The value of the contribution of segment `N` at time `t`, expressed through
the history before jump `M`, valid on the event that segment `M` is the active
one at `t`. -/
def davisSegmentContributionHistoryValue (S : SHS Q n m)
    (hflow : S.HasGlobalFlow) {Ω : Type*} (ξ : DavisJumpNoise m Ω)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) (N : ℕ) (t : ℝ≥0)
    (M : ℕ) (ω : Ω) : ℝ :=
  if N < M then davisSegmentCompletedContribution S hflow ξ initial g N ω
  else if N = M then
    -davisSegmentResetOccupationCompensator S hflow g
      (davisStateAfterJump S hflow ξ initial N ω) (t - ξ.jumpTime N ω)
  else 0

/-- The history form of a segment contribution is observable in the pre-jump
history at the index of the active segment. -/
theorem DavisJumpNoise.measurable_segmentContributionHistoryValue
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n)
    {g : DavisState Q n → ℝ} (hg : Measurable g)
    (hreg : DavisResetOccupationRegular S hflow g) (N : ℕ) (t : ℝ≥0) (M : ℕ) :
    Measurable[ξ.preJumpHistoryFiltration S hflow hf hr hξ initial M]
      (davisSegmentContributionHistoryValue S hflow ξ initial g N t M) := by
  unfold davisSegmentContributionHistoryValue
  by_cases hNM : N < M
  · simp only [if_pos hNM]
    exact (ξ.measurable_segmentCompletedContribution_preJumpHistory S hflow hf
      hr hξ initial hg hreg N).mono
      ((ξ.preJumpHistoryFiltration S hflow hf hr hξ initial).mono hNM) le_rfl
  · simp only [if_neg hNM]
    by_cases hNM' : N = M
    · simp only [if_pos hNM']
      subst hNM'
      exact (hreg.stoppedCompensator_measurable.comp
        ((ξ.measurable_stateAfterJump_preJumpHistory S hflow hf hr hξ initial N
            N le_rfl).prodMk
          (measurable_const.sub (ξ.measurable_jumpTime_preJumpHistory S hflow
            hf hr hξ initial N)))).neg
    · simp only [if_neg hNM']
      exact measurable_const

omit [MeasurableSpace Q] [MeasurableSingletonClass Q] in
/-- On the event that segment `M` is the active one at `t`, the contribution of
segment `N` is its history form. -/
theorem davisElapsedOccupationSegmentContribution_eq_historyValue
    (S : SHS Q n m) (hflow : S.HasGlobalFlow) {Ω : Type*}
    (ξ : DavisJumpNoise m Ω) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) (g : DavisState Q n → ℝ) (N : ℕ) (t : ℝ≥0)
    (M : ℕ) (ω : Ω) (hω : ω ∈ ξ.activeEvent M t) :
    davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N t ω =
      davisSegmentContributionHistoryValue S hflow ξ initial g N t M ω := by
  rw [davisElapsedOccupationSegmentContribution_eq_ite_jumpTime]
  unfold davisSegmentContributionHistoryValue
  rcases lt_trichotomy N M with hlt | heq | hgt
  · have hsucc : ξ.jumpTime (N + 1) ω ≤ t :=
      le_trans (ξ.jumpTime_mono ω (Nat.succ_le_of_lt hlt)) hω.1
    rw [if_pos hsucc, if_pos hlt]
  · subst heq
    have hsucc : ¬ ξ.jumpTime (N + 1) ω ≤ t := hω.2
    rw [if_neg hsucc, if_pos hω.1, if_neg (lt_irrefl N), if_pos rfl]
  · have hstart : ¬ ξ.jumpTime N ω ≤ t := by
      intro hcon
      exact hω.2 (le_trans (ξ.jumpTime_mono ω (Nat.succ_le_of_lt hgt)) hcon)
    have hsucc : ¬ ξ.jumpTime (N + 1) ω ≤ t := fun hcon =>
      hstart (le_trans (ξ.jumpTime_mono ω (Nat.le_succ N)) hcon)
    rw [if_neg hsucc, if_neg hstart, if_neg (not_lt.2 (le_of_lt hgt)),
      if_neg (Nat.ne_of_gt hgt)]

/-! ## Observability of the segment contribution -/

/-- **The contribution of a segment is observable.**  At every time, the
contribution of segment `N` is measurable for the observation filtration of the
marked jump history. -/
theorem DavisJumpNoise.measurable_markedJump_segmentContribution
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (hne : ξ.NonExplosive)
    (initial : DavisState Q n) {g : DavisState Q n → ℝ} (hg : Measurable g)
    (hreg : DavisResetOccupationRegular S hflow g) (N : ℕ) (t : ℝ≥0) :
    Measurable[ξ.markedJumpSpace S hflow hf hr hξ initial t]
      (davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N
        t) := by
  intro E hE M
  refine ⟨(davisSegmentContributionHistoryValue S hflow ξ initial g N t M) ⁻¹' E
      ∩ {ω | ξ.jumpTime M ω ≤ t}, ?_, ?_, ?_⟩
  · exact ((ξ.measurable_segmentContributionHistoryValue S hflow hf hr hξ
      initial hg hreg N t M) hE).inter
      (ξ.measurableSet_jumpTime_le_preJumpHistory S hflow hf hr hξ initial M M
        le_rfl t)
  · exact fun ω hω => hω.2
  · ext ω
    constructor
    · rintro ⟨hωE, hωact⟩
      refine ⟨⟨?_, hωact.1⟩, hωact⟩
      have heq := davisElapsedOccupationSegmentContribution_eq_historyValue S
        hflow ξ hne initial g N t M ω hωact
      show davisSegmentContributionHistoryValue S hflow ξ initial g N t M ω ∈ E
      rw [← heq]
      exact hωE
    · rintro ⟨⟨hωE, -⟩, hωact⟩
      refine ⟨?_, hωact⟩
      have heq := davisElapsedOccupationSegmentContribution_eq_historyValue S
        hflow ξ hne initial g N t M ω hωact
      show davisElapsedOccupationSegmentContribution S hflow ξ hne initial g N t
        ω ∈ E
      rw [heq]
      exact hωE

/-- Cumulative jump times are observable for the marked jump filtration. -/
theorem DavisJumpNoise.measurableSet_markedJump_jumpTime_le
    (S : SHS Q n m) (hflow : S.HasGlobalFlow)
    (hf : DavisFlowRegular S hflow) (hr : DavisResetRegular S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (ξ : DavisJumpNoise m Ω)
    (hξ : ξ.MeasurableNoise) (initial : DavisState Q n) (k : ℕ) (t : ℝ≥0) :
    MeasurableSet[ξ.markedJumpSpace S hflow hf hr hξ initial t]
      {ω | ξ.jumpTime k ω ≤ t} := by
  intro M
  by_cases hkM : k ≤ M
  · refine ⟨{ω | ξ.jumpTime k ω ≤ t} ∩ {ω | ξ.jumpTime M ω ≤ t}, ?_, ?_, ?_⟩
    · exact (ξ.measurableSet_jumpTime_le_preJumpHistory S hflow hf hr hξ initial
        k M hkM t).inter
        (ξ.measurableSet_jumpTime_le_preJumpHistory S hflow hf hr hξ initial M M
          le_rfl t)
    · exact fun ω hω => hω.2
    · ext ω
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  · refine ⟨∅, @MeasurableSet.empty Ω
      (ξ.preJumpHistorySpace S hflow initial M), by simp, ?_⟩
    ext ω
    constructor
    · rintro ⟨hωk, hωact⟩
      exact absurd (le_trans (ξ.jumpTime_mono ω
        (Nat.succ_le_of_lt (Nat.lt_of_not_le hkM))) hωk) hωact.2
    · rintro ⟨hωe, -⟩
      exact absurd hωe (Set.notMem_empty ω)

end SHS
